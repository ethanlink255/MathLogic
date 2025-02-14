; Declare two Boolean variables
(declare-const a Bool)
(declare-const b Bool)

; Define the add operation: a XOR b

(define-fun add ((x Bool) (y Bool)) Bool
  (and (or x y) (not (and x y)))
)

; what do I write here?

(assert (= a true))
(assert (= b false))

(assert (= (add a b) false))

; 3 seperate examples of SAT assignments

; Check satisfiability
(check-sat)

; Get the model if satisfiable
(get-model)


