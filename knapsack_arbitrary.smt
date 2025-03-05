(set-logic QF_LIA) 

; Declare problem parameters
(declare-const C Int)  ; Knapsack capacity

; Declare item weights
(declare-const w1 Int)
(declare-const w2 Int)
(declare-const w3 Int)
(declare-const w4 Int)

; an arbitrary way to encode some number of items?

; Declare integer selection variables constrained to {0,1}
(declare-const x1 Int); 0 
(declare-const x2 Int); 1
(declare-const x3 Int); 0
(declare-const x4 Int); 1

(assert (and (<= 0 x1) (<= x1 1)))
(assert (and (<= 0 x2) (<= x2 1)))
(assert (and (<= 0 x3) (<= x3 1)))
(assert (and (<= 0 x4) (<= x4 1)))


; Ensure the total weight does not exceed capacity
(assert (= (+ (* x1 w1) (* x2 w2) (* x3 w3) (* x4 w4)) C))

; Example item weights and capacity (uncomment to run with a specific instance)
(assert (= C 10))
(assert (= w1 3))
(assert (= w2 4))
(assert (= w3 5))
(assert (= w4 6))

; Check satisfiability and return a model
(check-sat)
(get-model)