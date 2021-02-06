(assert-eq (cons 1 2) '(1 . 2))

(assert-eq (list 1 2 3) '(1 2 3))

(define x '(1 . 2))
(assert-eq (car x) 1)
(assert-eq (cdr x) 2)

(define x '(1 . 2))
(set-car! x 123)
(assert-eq x '(123 . 2))
(set-cdr! x 456)
(assert-eq x '(123 . 456))

(define x '(1 . 2))
(set-car! x ())
(set-cdr! x ())
(assert-eq x '(() . ()))

(define x '(1 . 2))
(assert-error
  (lambda() (set-car! x '(1)))
  '(Unsafe))
(assert-error
  (lambda() (set-cdr! x '(1)))
  '(Unsafe))
(unsafe-set-car! x '(1))
(unsafe-set-cdr! x '(2))
(assert-eq x '((1) . (2)))
