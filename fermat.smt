(set-logic QF_NIA)

; Declare exponent variable n and constrain it between 1 and 1000.
(declare-const n Int)
(assert (and (>= n 2) (<= n 1000)))

; Define a recursive function to compute x^n.

; (define-fun-rec factorial ((n Int)) Int
;   (if (<= n 0) 
;       1 
;       (* n (factorial (- n 1))))) 

;tail recursion
(define-fun-rec pow ((num Int) (power Int)) Int
  (ite (= power 0)
       1
       (* num (pow num (- power 1)))))

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)

(assert (> a 1))
(assert (> b 1))
(assert (> c 1))

(assert (distinct a b c))

; Assert the fermats theorem: a^n + b^n = c^n.
(assert (= (+ (pow a n) (pow b n)) (pow c n)))


(check-sat)
(get-model)

(assert (distinct n 492))

(check-sat)
(get-model)


(assert (distinct n 2))

(check-sat)
(get-model)

(assert (distinct n 3))

(check-sat)
(get-model)

;; continued adding constraints
; until UNSAT