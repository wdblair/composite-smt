(declare-fun A () Bool)
;; (set-option :print-success false)
(declare-sort U 0)
(declare-fun B (U) Bool)
(declare-fun x () U)
(assert (= A (B x)))
(assert (not A))
(push 1)
(define-fun C () Bool (B x))
(assert C)
(check-sat)
(pop 1)
(define-fun C () Int 1)
(exit)
