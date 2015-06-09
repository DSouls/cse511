; TODOS
;	post-gridlock logic
;	pre-gridlock logic

; ***************************************************************************
; ***************************************************************************
;
; Program Description
; 
;
; ***************************************************************************
; ***************************************************************************

(defmodule MAIN
	(export deftemplate ?ALL)
	(export defglobal num-lines num-moves)
)

; ***************************************************************************
;
; SYSTEM KNOWLEDGE
;
; Description: Contains templates and global variables used by the system
;
; ***************************************************************************

(defglobal MAIN
	?*num-rows* = 0             ;Number of rows in the game defined as boxes
	?*num-columns* = 0          ;Number of columns in the game defined as boxes
	?*num-lines* = 0            ;Total number of lines used to make up the playfield
	?*num-moves* = 0            ;Current number of moves taken by players
	?*player-score* = 0         ;Number of boxes completed by this program
	?*opponent-score* = 0       ;Number of boxes completed by the opponent from input
)

(deftemplate MAIN::line-data "Keeps track of which lines are marked"
	(slot number (type INTEGER) (range 1 ?VARIABLE))
	(slot marked (type SYMBOL) (allowed-symbols yes no))
)

(deftemplate MAIN::box-data "Keeps track of the completion state of boxes"
	(multislot open-sides (type INTEGER) (range 1 ?VARIABLE))
	(slot point-value (type INTEGER))
)

(deftemplate MAIN::move "Line chosen by a player to mark next"
	(slot line (type INTEGER) (range 1 ?VARIABLE))
)

(deftemplate MAIN::active-player "Monitors who the active player is"
	(slot who (type SYMBOL) (allowed-symbols player opponent))
)

; ***************************************************************************
;
; INITIALIZATION
;
; Description: Creates the game board and initializes play
;
; ***************************************************************************

(defrule MAIN::generate-playfield "Determines the size of the game board"
	(test (eq ?*num-rows* 0))
	(test (eq ?*num-columns* 0))
=>
	(printout t "Number of rows?" crlf)
	(bind ?*num-rows* (read))
	(while (< ?*num-rows* 1) do
		(printout t "Invalid number. Please enter a new number of rows." crlf)
		(bind ?*num-rows* (read))
	)
	(printout t "Number of columns?" crlf)
	(bind ?*num-columns* (read))
	(while (< ?*num-columns* 1) do
		(printout t "Invalid number. Please enter a new number of columns." crlf)
		(bind ?*num-columns* (read))
	)
	(assert (initialize))
)

(defrule MAIN::initialize "Creates all applicable lines for the game and sets player status"
	?initialize-fact <- (initialize)
	(test (eq ?*num-lines* 0))
=>
	(bind ?horizontal-moves (* (+ ?*num-rows* 1) ?*num-columns*))
	(bind ?vertical-moves (* (+ ?*num-columns* 1) ?*num-rows*))
	(bind ?*num-lines* (+ ?horizontal-moves ?vertical-moves))
	(loop-for-count (?i 1 ?*num-lines*) do
		(assert (line-data (number ?i) (marked no)))
	)
	(loop-for-count (?i 1 ?*num-rows*)
		(loop-for-count (?j 1 ?*num-columns*)
			(bind ?side1 (+ ?j (* ?*num-columns* (- ?i 1))))
			(bind ?side2 (+ ?horizontal-moves ?j (* (- ?i 1) (+ ?*num-columns* 1)) 1))
			(bind ?side3 (+ ?side1 ?*num-columns*))
			(bind ?side4 (- ?side2 1))
			(assert (box-data (open-sides ?side1 ?side2 ?side3 ?side4) (point-value 1)))
		)
	)
	(retract ?initialize-fact)
	(printout t "Ready to play." crlf)
	(printout t "Am I playing first or second?" crlf)
	(bind ?position (read))
	(while (and (neq ?position first) (neq ?position second))
		(printout t "Invalid response. Type \"first\" or \"second\" without quotes." crlf)
		(bind ?position (read))
	)
	(if (eq ?position first)
	 then
		(assert (active-player (who player)))
	 else
		(assert (active-player (who opponent)))
	)
)

; ***************************************************************************
;
; GAME MEDIATION
;
; Description: Maintains current game state and switches whose turn it is
;
; ***************************************************************************

(defrule MAIN::switch-turn "Mediates changing of active player"
	(declare (salience -1))
	?active-player-fact <- (active-player)
=>
	(if (eq (fact-slot-value ?active-player-fact who) player)
	 then
		(modify ?active-player-fact (who opponent))
	 else
		(modify ?active-player-fact (who player))
	)
)

(defrule MAIN::gridlock-awareness "Checks for gridlock to change logic"
	(declare (auto-focus TRUE))
	(forall
		(box-data (open-sides $?lines))
		(test (eq (length $?lines) 2))
	)
=>
	(assert (gridlock))
)	

(defrule MAIN::game-over "Quits the program"
	(declare (salience 1))
	(active-player)
	(not (exists (line-data (marked no))))
=>
	(printout t "Game is over." crlf)
	(printout t "Player score: " ?*player-score* crlf "Opponent score: " ?*opponent-score* crlf)
	(if (eq ?*player-score* ?*opponent-score*)
	 then
		(printout t "Draw." crlf)
	 else
		(if (> ?*player-score* ?*opponent-score*)
		 then
			(printout t "I win." crlf)
		 else
			(printout t "Opponent wins." crlf)
		)
	)
	(halt)
)

(defrule MAIN::modify-boxes "Removes line from relevant box data or increases points for a domino"
	(move (line ?line))
	?old-box-status <- (box-data (open-sides $?lines-before ?line $?lines-after) (point-value ?points))
	?active-player-fact <- (active-player)
=>
	(if (not (duplicate ?old-box-status (open-sides $?lines-before $?lines-after)))
	 then
		(assert (domino-exists))
	 else
	 	(retract ?old-box-status)
		(if (and (eq (length $?lines-before) 0) (eq (length $?lines-after) 0))
		 then
			(assert (add-points))
		)
	)
)

(defrule MAIN::increase-box-points "Increase point values for a double cross move"
	?domino-exists-fact <- (domino-exists)
	(move (line ?line))
	?domino-half-1 <- (box-data (open-sides $?lines-before ?line $?lines-after))
	?domino-half-2 <- (box-data (open-sides $?lines-before $?lines-after))
=>
	(modify ?domino-half-2 (point-value 2))
	(retract ?domino-half-1)
	(retract ?domino-exists-fact)
)

(defrule MAIN::add-points "Assigns points to players for completed boxes"
	?add-points-fact <- (add-points)
	?completed-box <- (box-data (open-sides $?lines) (point-value ?points))
	(test (eq (length $?lines) 0))
	?active-player-fact <- (active-player)
=>
	(if (eq (fact-slot-value ?active-player-fact who) player)
	 then
		(bind ?*player-score* (+ ?*player-score* ?points))
	 else
		(bind ?*opponent-score* (+ ?*opponent-score* ?points))
	)
	(retract ?add-points-fact)
	(retract ?completed-box)
)

(defrule MAIN::mark-line "Marks lines used in moves for record keeping"
	?move-fact <- (move (line ?line))
	?line-status <- (line-data (number ?line) (marked ?mark))
	(not (box-data (open-sides $?lines-before ?line $?lines-after)))
	?active-player-fact <- (active-player)
=>
	(modify ?line-status (marked yes))
	(bind ?*num-moves* (+ ?*num-moves* 1))
	(assert (return-control))
	(retract ?move-fact)
)

(defrule MAIN::return-control "Returns control to the active player"
	?return-control-fact <- (return-control)
	?active-player-fact <- (active-player)
=>
	(if (eq (fact-slot-value ?active-player-fact who) player)
	 then
		(focus INITIAL-PLAYER-LOGIC)
	 else
		(focus OPPONENT-MOVE)
	)
	(retract ?return-control-fact)
)	

; ***************************************************************************
;
; OPPONENT MOVE
;
; Description: Gets moves from opponent and validates user input
;
; ***************************************************************************

(defmodule OPPONENT-MOVE
	(import MAIN deftemplate active-player line-data move)
	(import MAIN defglobal num-lines)
)

(defglobal OPPONENT-MOVE
	?*num-opponent-moves* = 0   ;Ensures at least one move is made by the opponent
)

(defrule OPPONENT-MOVE::start-opponent-move "Prints out the initial moves request prompt"
	(declare (auto-focus TRUE))
	(active-player (who opponent))
=>
	(printout t "Please enter the moves from the opponent separated by newlines. Type done when finished." crlf)
	(assert (get-move))
)

(defrule OPPONENT-MOVE::get-move "Gets moves made by opponent, ensuring at least one"
	?get-move-fact <- (get-move)
=>
	(bind ?move (read))
	(if (eq ?move done)
	 then
		(assert (check-moves))
	 else
		(assert (opponent-move ?move))
	)
	(retract ?get-move-fact)
)

(defrule OPPONENT-MOVE::num-moves-check "Check to make sure at least one valid move has been made"
	?check-moves-fact <- (check-moves)
=>
	(if (= 0 ?*num-opponent-moves*)
	 then
		(printout t "Please enter at least one valid move." crlf)
		(assert (get-move))
	 else
		(bind ?*num-opponent-moves* 0)
	)
	(retract ?check-moves-fact)
)

(defrule OPPONENT-MOVE::opponent-input-validation "Ensures the opponent input is not a miscellaneous string"
	?move-fact <- (opponent-move ?move)
	(test (not (integerp ?move)))
=>
	(printout t "Invalid input. Please try again." crlf)
	(retract ?move-fact)
	(assert (get-move))
)

(defrule OPPONENT-MOVE::invalid-opponent-move "Move is not within the correct range"
	?move-fact <- (opponent-move ?line)
	(test (integerp ?line))
	(test (not (and (> ?line 0) (<= ?line ?*num-lines*))))
=>
	(printout t "Line number out of range. Please try again." crlf)
	(retract ?move-fact)
	(assert (get-move))
)

(defrule OPPONENT-MOVE::valid-opponent-move "Move is within the correct range"
	?move-fact <- (opponent-move ?line)
=>
	(retract ?move-fact)
	(assert (check-line ?line))
)

(defrule OPPONENT-MOVE::check-line "Check if line is already marked and handle appropriately"
	?check-line-fact <- (check-line ?line)
	(line-data (number ?line) (marked ?mark))
=>
	(assert (get-move))
	(if (eq ?mark yes)
	 then
		(printout t ?line " is already marked. Re-enter or ignore if unintended." crlf)
	 else
		(assert (move (line ?line)))
		(bind ?*num-opponent-moves* (+ ?*num-opponent-moves* 1))
		(focus MAIN)
	)
	(retract ?check-line-fact)
)

; ***************************************************************************
;
; PLAYER MOVE
;
; Description: Determines the move the AI will take next
;
; ***************************************************************************

(defmodule INITIAL-PLAYER-LOGIC
	(import MAIN deftemplate ?ALL)
	(import MAIN defglobal num-moves num-lines)
)

(defrule INITIAL-PLAYER-LOGIC::start-player-move "Begins mediation of player logic"
	(declare (auto-focus TRUE))
	(active-player (who player))
=>
	(printout t "I choose: ")
	(assert (make-move))
)

(defrule INITIAL-PLAYER-LOGIC::finish-box "Closes a box if only one line is left"
	(make-move)
	(box-data (open-sides ?remaining-side $?other-sides))
	(test (= (length $?other-sides) 0))
=>
	(if (eq (+ ?*num-moves* 1) ?*num-lines*)
	 then
		(printout t ?remaining-side crlf)
		(focus MAIN)
	 else
		(printout t ?remaining-side " ")
	)
	(assert (move (line ?remaining-side)))
)

(defrule INITIAL-PLAYER-LOGIC::default-move "Moderates the choosing of a random line"
	?make-move-fact <- (make-move)
=>
	(retract ?make-move-fact)
	(assert (random-move))
)

(defrule INITIAL-PLAYER-LOGIC::random-move "Picks a random line"
	?random-move-fact <- (random-move)
=>
	(seed (round (time)))
	(bind ?line (+ (mod (random) ?*num-lines*) 1))
	(assert (choose-line ?line))
	(retract ?random-move-fact)
)

(defrule INITIAL-PLAYER-LOGIC::valid-player-move "Ensures move is valid and takes it"
	?choose-line-fact <- (choose-line ?line)
	(line-data (number ?line) (marked no))
=>
	(printout t ?line crlf)
	(assert (move (line ?line)))
	(retract ?choose-line-fact)
	(focus MAIN)
)

(defrule INITIAL-PLAYER-LOGIC::invalid-player-move "Generates a new choice if move is invalid"
	?choose-line-fact <- (choose-line ?line)
=>
	(assert (random-move))
	(retract ?choose-line-fact)
)