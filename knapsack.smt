(set-logic QF_BV) 

(define-fun x1 () (_ BitVec 3) #b001)  
(define-fun x2 () (_ BitVec 3) #b011) 
(define-fun x3 () (_ BitVec 3) #b010) 

(define-fun c () (_ BitVec 3) #b100)


(define-fun fancy ((x_1 (_ BitVec 3)) (x_2 (_ BitVec 3))) (Bool) 
    (= c (bvadd x_1 x_2))
)

(declare-fun x_1_p () (_ BitVec 3))
(declare-fun x_2_p () (_ BitVec 3))

(assert (or (= x_1_p x1) (= x_1_p x2) (= x_1_p x3)))
(assert (or (= x_2_p x1) (= x_2_p x2) (= x_2_p x3)))
(assert (distinct x_1_p x_2_p))

(assert (fancy x_1_p x_2_p))

(check-sat)
(get-model)