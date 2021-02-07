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

(assert-eq
  ((lambda (x)
     ((lambda (y z)
        ((lambda (x z) (list x y z)) 'x2 'z2)) 'y 'z)) 'x)
  (list 'x2 'y 'z2))

(define set-x ())
(define get-x ())
((lambda (x)
    (set-local! x 1)
    (set-global! set-x (lambda (v) (set-local! x v)))
    (set-global! get-x (lambda () x))
    (set-local! x 2)) 0)
(assert-eq (get-x) 2)
(set-x 3)
(assert-eq (get-x) 3)
