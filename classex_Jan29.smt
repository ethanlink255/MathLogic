
;; Think of a small situation that encodes some amount state
;; Washing machine
;; {v1 - is washing, v2 - is rinsing, v3 - is spinning, v4 - is drying}
;; (0000) -> {(1000), (0100), (0010), (0001)} -> ...
;; (1000) -> (0100) -> {(0010), (0001)} 
;; (0100) -> {(0010), (0001)} $ this is a redudant rule
;; (0010) -> {(0000), (0001)}
;; (0001) -> (0000)

;(0000) -> (0001) ?
;(0000) -> (1000) -> (0001) ?

;(0000) -> (1000) -> (0010) ?



;; what must a washing machine do at some point? Halt

;; If a washing machine washes, it must eventually dry... ->
;; some other rule
;; your own situation, anything at all! 
;; It could never be washing and drying at the same time.
;; (assert (v1_? and v4_?))
;; define some behavior across states 
;; Washing machine must return to (0000), in arbitrarily many time steps!

; how do I solve this problem? How do I go about it? 
; What to do now?

; we need to encode those states!

; state 0
(declare-const washing_s0 Bool)
(declare-const rinsing_s0 Bool)
(declare-const spinning_s0 Bool)
(declare-const drying_s0 Bool)

; state 1
(declare-const washing_s1 Bool)
(declare-const rinsing_s1 Bool)
(declare-const spinning_s1 Bool)
(declare-const drying_s1 Bool)

; state 2
(declare-const washing_s2 Bool)
(declare-const rinsing_s2 Bool)
(declare-const spinning_s2 Bool)
(declare-const drying_s2 Bool)

; state 3
(declare-const washing_s3 Bool)
(declare-const rinsing_s3 Bool)
(declare-const spinning_s3 Bool)
(declare-const drying_s3 Bool)

; assert the starting state S0 == 0000
(assert (= false (or washing_s0 rinsing_s0 spinning_s0 drying_s0)))

; transitions :
;; (0000) -> {(1000), (0100), (0010), (0001)} -> ...

;; this is manually asserting that s1 must be in one of the four states above

(assert (= true (xor washing_s1 rinsing_s1 spinning_s1 drying_s1)))

;; (1000) -> (0100) -> {(0010), (0001)} 
; washing leads to rinsing deterministically, which then may lead to something else
; What if the machine wasn't washing in state s1? 
;; s0        s1         s2
;; (0000) -> (0100) -> ({0010, 0001})      Nothing in s0 -> rinsing in s1 -> leads to either spinning or drying in s2 DONE
;; (0000) -> (1000) -> (0100)   Nothing in s0 -> washing in s1 -> leads to rinsing in s2    DONE
;; (0000) -> (0010) -> {(0001), (0000)}         Nothing in s0 -> spinning in s1 -> leads to what in s2 DONE 
;; (0000) -> (0001) -> (0000)   Nothing in s0 -> drying in s1 -> Nothing in s2              DONE

; if washing in s1, rinse in s2
(assert (= washing_s2 false))
(assert (= rinsing_s2 washing_s1))


; if drying was happening in s1 THEN we must be in the state 0000 in s2
(assert (=> drying_s1 (= false (or washing_s2 rinsing_s2 spinning_s2 drying_s2))))

; if rinsing in s1 THEN we must dry or spin in s2
(assert (=> rinsing_s1 (xor spinning_s2 drying_s2)))

; if we spin in s1 THEN we MUST either dry in s2 or HALT
; NOTE: this implicitly codes for the first 3 bits of state to be low,
; while allowing drying to float, meaning it may take on an arbitrary value! (Logan)
(assert (=> spinning_s1 (= false (or washing_s2 rinsing_s2 spinning_s2))))

; fun question are the minimal statements equivalnet? The above and Eric's original statement 
; (assert (=> spinning_s1 (xor drying_s2 (= false (or washing_s2 rinsing_s2 spinning_s2 drying_s2)))

;(0000) -> (????) -> (0010) ?


(push) ; saves the state above on the stack 

(assert (= washing_s2 false))
(assert (= rinsing_s2 false))
(assert (= spinning_s2 true))
(assert (= drying_s2 false))


(check-sat)
(get-model)

(pop)

(push)

(assert (= washing_s2 false))
(assert (= rinsing_s2 true))
(assert (= spinning_s2 false))
(assert (= drying_s2 false))


(check-sat)
(get-model)

(pop)


; s0 washing rinsing spinning dyring  (0 0 0 0)

; s1 washing rinsing spinning drying  (0 1 0 0)


