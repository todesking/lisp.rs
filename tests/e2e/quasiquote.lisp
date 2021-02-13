(assert-eq '`1 '(quasiquote 1))
(assert-eq '`(,x) '(quasiquote ((unquote x))))
(assert-eq '`(,@x) '(quasiquote ((unquote-splicing x))))

(assert-error
  (lambda () ,1)
  '(QuasiQuote))
(assert-error
  (lambda () ,@1)
  '(QuasiQuote))
(assert-error
  (lambda () ``a)
  '(QuasiQuote))

(assert-eq `1 1)
(assert-eq `,1 1)
(assert-eq `(1 2 3) '(1 2 3))
(assert-eq `(1 ,2 3) '(1 2 3))
(assert-eq `(1 ,(+ 2 3) 3) '(1 5 3))
(assert-eq `(1 2 . ,3) '(1 2 . 3))

(assert-eq `(1 ,'(2 3 4) 5) '(1 (2 3 4) 5))
(assert-eq `(1 ,@'(2 3 4) 5) '(1 2 3 4 5))
(assert-error
  (lambda () `(,@1))
  '(QuasiQuote))
(assert-error
  (lambda () `,@'(1))
  '(QuasiQuote))
(assert-error
  (lambda () `(1 . ,@'(1 2)))
  '(QuasiQuote))

(assert-eq `(,@`(1 ,@'(2 3)) 4) '(1 2 3 4))
(assert-eq `(,@(list 1 2 3) . 4) '(1 2 3 . 4))
