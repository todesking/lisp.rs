(assert-error
  (lambda () g1)
  '(VariableNotFound g1))

(define g1 1)
(assert-eq g1 1)

(assert-eq
  ((lambda (x) x) 123)
  123)
(assert-eq
  ((lambda (x y g1) g1) 0 1 123)
  123)

(set-global! g1 123)
(assert-eq g1 123)

((lambda (g1) (set-global! g1 999)) 888)
(assert-eq g1 999)
