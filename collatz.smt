; Upper bounds
(declare-const N Int)  ; Upper bound for numbers to check
(declare-const S Int)  ; Maximum steps allowed

(assert (> N 1))  ; Ensure N > 1
(assert (> S 0))  ; Must allow at least 1 step

; Define the transition function for one step of Collatz
(define-fun collatz ((n Int)) Int
    (ite (= (mod n 2) 0) (div n 2) (+ (* 3 n) 1))
)


; defines, given some n, after some k applications of Collatz, what the result is
(declare-fun step (Int Int) Int)

; Base case: The first step is the number itself
(assert (forall ((n Int))
    (=> (and (> n 1) (<= n N))
        (= (step n 0) n)
    )
))

; Unroll the sequence for at most S steps
; creates a self referential function
; if (step n 0) = n then:
; for all n, k, (step n 1) = collatz (step n 0)
; which means that (step n 1) = collatz n
; SO...
; step n 2 = collatz step n 1
;          = collatz collatz n 
;
; and so on and so forth...
; so n up to some bound N in some nymber of time steps k, 
; we are able to find all collatz sequences

(assert (forall ((n Int) (k Int))
    (=> (and (> n 1) (<= n N) (>= k 0) (< k S))
        (= (step n (+ k 1)) (collatz (step n k)))
    )
))

; Now we need to state that for a given n, there exists 
; some k for which step n k is 1!

; Every number between 2 and N must reach 1 within S steps
(assert (forall ((n Int))
    (=> (and (> n 1) (<= n N))
        (exists ((k Int))
            (and (>= k 0) (< k S) (= (step n k) 1))
        )
    )
))

; Set test values for N and S
(assert (= N 7))   ; Check numbers up to 100
(assert (= S 17))   ; Allow at most 500 steps per number

; Check satisfiability
(check-sat)