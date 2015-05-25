; TODOS
;	point system (some points aren't being awarded {probably salience})
;	gridlock awareness
;	post-gridlock logic
;	pre-gridlock logic

;
; SYSTEM KNOWLEDGE
;

(defglobal
	?*num-rows* = 0
	?*num-columns* = 0
	?*num-lines* = 0
	?*num-moves* = 0
	?*player-score* = 0
	?*opponent-score* = 0
)

(deftemplate line-data "Keeps track of which lines are marked"
	(slot number (type INTEGER) (range 1 ?VARIABLE))
	(slot marked (type SYMBOL) (allowed-symbols yes no))
)

(deftemplate box-data "Keeps track of the completion state of boxes"
	(multislot open-sides (type INTEGER) (range 1 ?VARIABLE))
)

(deftemplate active-player "Monitors who the active player is"
	(slot who (type SYMBOL) (allowed-symbols player opponent))
)

;
; INITIALIZATION
;

(defrule generate-playfield "Determines the size of the game."
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

(defrule initialize "Creates all applicable lines for the game and sets player status."
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
			(assert (box-data (open-sides ?side1 ?side2 ?side3 ?side4)))
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

;
; GAME MEDIATION
;

(defrule switch-turn "Mediates changing of active player"
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

(defrule game-over "Quits the program"
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

(defrule modify-boxes "Removes line from relevant box data"
	(draw-line ?line)
	?old-box-status <- (box-data (open-sides $?lines-before ?line $?lines-after))
	?active-player-fact <- (active-player)
=>
	(if (and (eq (length $?lines-before) 0) (eq (length $?lines-after) 0))
	 then
		(if (eq (fact-slot-value ?active-player-fact who) player)
		 then
			(bind ?*player-score* (+ ?*player-score* 1))
			(printout t "Player score is now " ?*player-score* crlf)
		 else
			(bind ?*opponent-score* (+ ?*opponent-score* 1))
			(printout t "Opponent score is now " ?*opponent-score* crlf)
		)
	 else
		(duplicate ?old-box-status (open-sides $?lines-before $?lines-after))
	)
	(retract ?old-box-status)
)

(defrule mark-line "Marks lines used in moves for record keeping"
	?draw-line-fact <- (draw-line ?line)
	?line-status <- (line-data (number ?line) (marked ?mark))
	(not (box-data (open-sides $?lines-before ?line $?lines-after)))
=>
	(modify ?line-status (marked yes))
	(bind ?*num-moves* (+ ?*num-moves* 1))
	(retract ?draw-line-fact)
)	

;
; OPPONENT MOVE
;

(defrule start-opponent-move "Prints out the initial moves request prompt."
	(active-player (who opponent))
=>
	(printout t "Please enter the moves from the opponent separated by newlines. Type done when finished." crlf)
	(assert (get-move))
)

(defrule get-move "Gets moves made by opponent"
	?get-move-fact <- (get-move)
=>
	(bind ?move (read))
	(if (neq ?move done)
	 then
		(assert (opponent-move ?move))
	)
	(retract ?get-move-fact)
)

(defrule invalid-opponent-move "Move is not within the correct range"
	?move-fact <- (opponent-move ?line)
	(test (not (and (> ?line 0) (<= ?line ?*num-lines*))))
=>
	(printout t "Line number out of range. Please try again." crlf)
	(retract ?move-fact)
	(assert (get-move))
)

(defrule valid-opponent-move "Move is within the correct range"
	?move-fact <- (opponent-move ?line)
=>
	(retract ?move-fact)
	(assert (check-line ?line))
)

(defrule check-line "Check if line is already marked and handle appropriately."
	?check-line-fact <- (check-line ?line)
	(line-data (number ?line) (marked ?mark))
=>
	(if (eq ?mark yes)
	 then
		(printout t ?line " is already marked. Re-enter or ignore if unintended." crlf)
	 else
		(assert (draw-line ?line))
	)
	(retract ?check-line-fact)
	(assert (get-move))
)

;
; PLAYER MOVE
;

(defrule start-player-move "Begins mediation of player logic."
	(active-player (who player))
=>
	(printout t "I choose: ")
	(assert (make-move))
)

(defrule finish-box "Closes a box if only one line is left"
	(make-move)
	(box-data (open-sides ?remaining-side $?other-sides))
	(test (= (length $?other-sides) 0))
=>
	(if (eq (+ ?*num-moves* 1) ?*num-lines*)
	 then
		(printout t ?remaining-side crlf)
	 else
		(printout t ?remaining-side " ")
	)
	(assert (draw-line ?remaining-side))
)

(defrule default-move "Moderates the choosing of a random line"
	?make-move-fact <- (make-move)
=>
	(retract ?make-move-fact)
	(assert (random-move))
)

(defrule random-move "Picks a random line"
	?random-move-fact <- (random-move)
=>
	(seed (round (time)))
	(bind ?line (+ (mod (random) ?*num-lines*) 1))
	(assert (choose-line ?line))
	(retract ?random-move-fact)
)

(defrule valid-player-move "Ensures move is valid and takes it"
	?choose-line-fact <- (choose-line ?line)
	(line-data (number ?line) (marked no))
=>
	(printout t ?line crlf)
	(assert (draw-line ?line))
	(retract ?choose-line-fact)
)

(defrule invalid-player-move "Generates a new choice if move is invalid"
	?choose-line-fact <- (choose-line ?line)
=>
	(assert (random-move))
	(retract ?choose-line-fact)
)