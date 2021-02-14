(defmacro (my-if cond then else) `(if ,cond ,then ,else))
(assert-eq
  (macro-expand '(my-if (eq? 1 "a") #t false))
  '(if (eq? 1 "a") #t false))
(assert-eq
  (macro-expand '(lambda (x y . z) (lambda (x) (list x y z 'foo))))
  '(lambda (x y . z) (lambda (x) (list x y z 'foo))))
(assert-eq
  (macro-expand '`(1 ,2 ,@3 4))
  '`(1 ,2 ,@3 4))
(assert-eq
  (macro-expand '(if-match 0 (('a b _ b) 123) 456))
  '(if-match 0 (('a b _ b) (lambda (b) 123)) 456))
