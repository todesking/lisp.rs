(defmacro one
 (lambda ()
  '1))
(assert-eq (one) 1)
(assert-error
 (lambda () (one 123))
 '(Macro IllegalArgument 123))

(defmacro my-let1
 (lambda (def body . rest)
  (if-match def
   ((name expr)
    `((lambda (,name) ,body ,@rest) ,expr))
   (error 'my-let1-error))))

(assert-eq
  ((get-macro my-let1) '(x 1) '(+ x 1))
  '((lambda (x) (+ x 1)) 1))
(assert-eq
  (my-let1 (x (+ 1 2)) (+ x x))
  6)
(assert-error
 (lambda () (my-let1))
 '(Macro IllegalArgument))
(assert-error
 (lambda () (my-let1 x y))
 '(Macro User my-let1-error))
