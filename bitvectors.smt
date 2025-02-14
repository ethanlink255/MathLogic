(set-logic QF_BV)

; how to declare BVs
(declare-const v1 (_ BitVec 1))
(declare-const v2 (_ BitVec 1))
(declare-const v3 (_ BitVec 1))
;(declare-const name_of_bv (_ BitVec n)) where n is number of bits

(assert (= #b0 (bvadd v2 (bvmul v1 v2)))) ; v1*v2 + v2 = 0
(assert (= #b0 (bvadd v3 (bvmul v3 v2)))) ; v3*v2 + v3 = 0 
(assert (= #b0 (bvadd v1 (bvmul v3 v1)))) ; v3*v1 + v1 = 0

;(assert (= #b1 v1))
;(assert (= #b0 (bvand v1 v2 v3)))

; bvor, bvadd, bvmul, bvand - or, add, mul, and of fixed width bvs
; bvnot, bvudiv, bvshl, bvlshr

(assert (= #b1 (bvnot v2)))

; 1 + 1 mod 2 -> 0 
; v1 + v2 + v2 mod 2^3 -> 8 

(check-sat)
(get-model)
;(get-assignment)
(exit)
