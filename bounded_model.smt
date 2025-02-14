; declare variables
; 4 states -> 2 bits per state
; 8 variables

; v_1_1 is the first bit at state 1
; v_2_1 is the second bit at state 1

; state 0 
(declare-const v_1_0 Bool)
(declare-const v_2_0 Bool)

; state 1 
(declare-const v_1_1 Bool)
(declare-const v_2_1 Bool)

; state 2 
(declare-const v_1_2 Bool)
(declare-const v_2_2 Bool)

; state 3 
(declare-const v_1_3 Bool)
(declare-const v_2_3 Bool)

; assert starting state
(assert (= v_1_0 false))
(assert (= v_2_0 false))

;transitions here

(assert (= v_2_1 (not v_2_0))) ; continue the transitions...
(assert (= v_1_1 (xor v_1_0 v_2_0)))
(assert (= v_2_2 (not v_2_1)))
(assert (= v_1_2 (xor v_1_1 v_2_1)))
(assert (= v_2_3 (not v_2_2)))
(assert (= v_1_3 (xor (v_1_2 v_2_2))))
(assert (= v_2_0 (not v_2_3)))
(assert (= v_1_0 (xor v_1_3 v_2_3)))

;property here
; in no state except for state 3 are both variables high!

(assert (= (and v_1_0 v_2_0) false))
(assert (= (and v_1_1 v_2_1) false))
(assert (= (and v_1_2 v_2_2) false))
(assert (= (and v_1_3 v_2_3) true))

(check-sat)
(get-model)

;; Think of a small situation that encodes some amount state
;; Washing machine
;; {v1 - is washing, v2 - is rinsing, v3 - is spinning, v4 - is drying}
;; (0000) -> {(0100), (0010), (0001)} -> ...

;; If a washing machine washes, it must eventually dry... ->
;; some other rule
;; your own situation, anything at all! 
;; It could never be washing and drying at the same time.
;; (assert (v1_? and v4_?))