(assert-eq (cons 1 2) '(1 . 2))

(assert-eq (list 1 2 3) '(1 2 3))

(define x '(1 . 2))
(assert-eq (car x) 1)
(assert-eq (cdr x) 2)
