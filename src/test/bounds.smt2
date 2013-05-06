;; The two pairs of constraints come from a simple ATS program involving arrays
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)

;; The following is unsat (valid)

;; An int vector is given by
;; A[0] + A[1]*x1 + A[2]*x2 + ... + A[n]*xn >= 0
;; where >= is the operator given by the integer constraint

(push 1)
;; constraint 1
(assert (< (+ 1 (+ (* x0 0) (+ (* x1 1) (* x2 0)))) 0))
(assert (< (+ 0 (+ (* x0 (- 1)) (+ (* x1 1) (* x2 0)))) 0))
(assert (>= (+ 0 (+ (* x0 0) (+ (* x1 1) (* x2 0)))) 0))
(assert (>= (+ 0 (+ (* x0 1) (+ (* x1 0) (* x2 0)))) 0))

(check-sat)
(pop 1)
;; constraint 2
(push 1)
(assert (>= (+ 0 (* x0 (- 1)) (+ (* x1 1) (* x2 0))) 0))
(assert (< (+ 0 (* x0 (- 1)) (+ (* x1 1) (* x2 0))) 0))
(assert (>= (+ 0 (+ (* x0 0) (+ (* x1 1) (* x2 0)))) 0))
(assert (>= (+ 0 (+ (* x0 1) (+ (* x1 0) (* x2 0)))) 0))

(check-sat)
(pop 1)

;; Both of these should give unsat (valid)

(push 1)
;; constraint 1
(assert (< 0 (+ (* x0 0) (+ (* x1 1) (* x2 0)))))
(assert (< 0 (+ (* x0 (- 1)) (+ (* x1 1) (* x2 0)))))
(assert (>= 0 (+ (* x0 0) (+ (* x1 1) (* x2 0)))))
(assert (>= 0 (+ (* x0 1) (+ (* x1 0) (* x2 0)))))

(check-sat)

(pop 1)
;; constraint 2
(push 1)
(assert (>= 0 (+ (* x0 (- 1)) (+ (* x1 1) (* x2 0)))))
(assert (< 0 (+ (* x0 (- 1)) (+ (* x1 1) (* x2 0)))))
(assert (>= 0 (+ (* x0 0) (+ (* x1 1) (* x2 0)))))
(assert (>= 0 (+ (* x0 1) (+ (* x1 0) (* x2 0)))))
(check-sat)
(pop 1)


;; Both of these should give unsat (valid)

(push 1)
;; constraint 1
(assert (< 0 (+ (* x0 0) (+ (* x1 1) (* x2 0)))))
(assert (< 0 (+ (* x0 (- 1)) (+ (* x1 1) (* x2 0)))))
(assert (>= 0 (+ (* x0 0) (+ (* x1 1) (* x2 0)))))
(assert (>= 0 (+ (* x0 1) (+ (* x1 0) (* x2 0)))))

(check-sat)

(pop 1)
;; constraint 2
(push 1)
(assert (>= 0 (+ (* x0 (- 1)) (+ (* x1 1) (* x2 0)))))
(assert (< 0 (+ (* x0 (- 1)) (+ (* x1 1) (* x2 0)))))
(assert (>= 0 (+ (* x0 0) (+ (* x1 1) (* x2 0)))))
(assert (>= 0 (+ (* x0 1) (+ (* x1 0) (* x2 0)))))
(check-sat)
(pop 1)


;; Both of these should give unsat (valid)

(push 1)
;; constraint 1
(assert (< 0 (+ (* x0 0) (+ (* x1 1) (* x2 0)))))
(assert (< 0 (+ (* x0 (- 1)) (+ (* x1 1) (* x2 0)))))
(assert (>= 0 (+ (* x0 0) (+ (* x1 1) (* x2 0)))))
(assert (>= 0 (+ (* x0 1) (+ (* x1 0) (* x2 0)))))

(check-sat)

(pop 1)
;; constraint 2
(push 1)
(assert (>= 0 (+ (* x0 (- 1)) (+ (* x1 1) (* x2 0)))))
(assert (< 0 (+ (* x0 (- 1)) (+ (* x1 1) (* x2 0)))))
(assert (>= 0 (+ (* x0 0) (+ (* x1 1) (* x2 0)))))
(assert (>= 0 (+ (* x0 1) (+ (* x1 0) (* x2 0)))))
(check-sat)
(pop 1)


;; Both of these should give unsat (valid)

(push 1)
;; constraint 1
(assert (< 0 (+ (* x0 0) (+ (* x1 1) (* x2 0)))))
(assert (< 0 (+ (* x0 (- 1)) (+ (* x1 1) (* x2 0)))))
(assert (>= 0 (+ (* x0 0) (+ (* x1 1) (* x2 0)))))
(assert (>= 0 (+ (* x0 1) (+ (* x1 0) (* x2 0)))))

(check-sat)

(pop 1)
;; constraint 2
(push 1)
(assert (>= 0 (+ (* x0 (- 1)) (+ (* x1 1) (* x2 0)))))
(assert (< 0 (+ (* x0 (- 1)) (+ (* x1 1) (* x2 0)))))
(assert (>= 0 (+ (* x0 0) (+ (* x1 1) (* x2 0)))))
(assert (>= 0 (+ (* x0 1) (+ (* x1 0) (* x2 0)))))
(check-sat)
(pop 1)


;; Both of these should give unsat (valid)

(push 1)
;; constraint 1
(assert (< 0 (+ (* x0 0) (+ (* x1 1) (* x2 0)))))
(assert (< 0 (+ (* x0 (- 1)) (+ (* x1 1) (* x2 0)))))
(assert (>= 0 (+ (* x0 0) (+ (* x1 1) (* x2 0)))))
(assert (>= 0 (+ (* x0 1) (+ (* x1 0) (* x2 0)))))

(check-sat)

(pop 1)
;; constraint 2
(push 1)
(assert (>= 0 (+ (* x0 (- 1)) (+ (* x1 1) (* x2 0)))))
(assert (< 0 (+ (* x0 (- 1)) (+ (* x1 1) (* x2 0)))))
(assert (>= 0 (+ (* x0 0) (+ (* x1 1) (* x2 0)))))
(assert (>= 0 (+ (* x0 1) (+ (* x1 0) (* x2 0)))))
(check-sat)
(pop 1)

;; Both of these should give unsat (valid)

(push 1)
;; constraint 1
(assert (< 0 (+ (* x0 0) (+ (* x1 1) (* x2 0)))))
(assert (< 0 (+ (* x0 (- 1)) (+ (* x1 1) (* x2 0)))))
(assert (>= 0 (+ (* x0 0) (+ (* x1 1) (* x2 0)))))
(assert (>= 0 (+ (* x0 1) (+ (* x1 0) (* x2 0)))))

(check-sat)

(pop 1)
;; constraint 2
(push 1)
(assert (>= 0 (+ (* x0 (- 1)) (+ (* x1 1) (* x2 0)))))
(assert (< 0 (+ (* x0 (- 1)) (+ (* x1 1) (* x2 0)))))
(assert (>= 0 (+ (* x0 0) (+ (* x1 1) (* x2 0)))))
(assert (>= 0 (+ (* x0 1) (+ (* x1 0) (* x2 0)))))
(check-sat)
(pop 1)


;; Both of these should give unsat (valid)

(push 1)
;; constraint 1
(assert (< 0 (+ (* x0 0) (+ (* x1 1) (* x2 0)))))
(assert (< 0 (+ (* x0 (- 1)) (+ (* x1 1) (* x2 0)))))
(assert (>= 0 (+ (* x0 0) (+ (* x1 1) (* x2 0)))))
(assert (>= 0 (+ (* x0 1) (+ (* x1 0) (* x2 0)))))

(check-sat)

(pop 1)
;; constraint 2
(push 1)
(assert (>= 0 (+ (* x0 (- 1)) (+ (* x1 1) (* x2 0)))))
(assert (< 0 (+ (* x0 (- 1)) (+ (* x1 1) (* x2 0)))))
(assert (>= 0 (+ (* x0 0) (+ (* x1 1) (* x2 0)))))
(assert (>= 0 (+ (* x0 1) (+ (* x1 0) (* x2 0)))))
(check-sat)
(pop 1)
