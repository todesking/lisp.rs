(define capture-error
  (lambda (f)
    (catch-error (lambda (e x) (cons e x))
      (f))))

(assert-error (lambda () (error 1)) '(User 1))

(assert-eq
  (capture-error (lambda () (assert-error (lambda () (error 1)) '(User 1))))
  ())

(assert-eq
  (capture-error (lambda () (assert-error (lambda () (error 1)) '(User 2))))
  (list 'User 'assert-eq '(User 1) '(User 2)))
