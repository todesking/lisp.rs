; numeric literal
(assert-eq (if-match 1 (1 #t) #f) #t)
(assert-eq (if-match 2 (1 #t) #f) #f)

; boolean literal
(assert-eq (if-match #f (#f #t) #f) #t)
(assert-eq (if-match #t (#f #t) #f) #f)

; capture
(assert-eq
  (if-match 1 (x x) ())
  1)

; capture-and-compare
(assert-eq
 (if-match '(1 2 1) ((x y x) (cons x y)) #f)
 '(1 . 2))
(assert-eq
 (if-match '(1 2 3) ((x y x) (cons x y)) #f)
 #f)

; list + capture
(assert-eq
 (if-match '(1 2 3)
  ((1 x 3) x) #f)
 2)
(assert-eq
 (if-match '(1 2 4)
  ((1 x 3) x) #f)
 #f)

; cons
(assert-eq
  (if-match '(1 2 3)
   ((a . b) b) #f)
  '(2 3))
(assert-eq
  (if-match 123
   ((a . b) b) #f)
  #f)

; quote
(assert-eq
 (if-match '(x y z)
  (('x ? 'z) ?) #f)
 'y)
(assert-eq
 (if-match '(x y x)
  (('x ? 'z) ?) #f)
 #f)

; any
(assert-eq
 (if-match 123 (_ #t) #f)
  #t)
(assert-eq
 (if-match '(1 2 3)
  ((a _ _) a) #f)
 1)
(assert-eq
 (if-match '(1 2)
  ((a _ _) a) #f)
 #f)

(define f
 (lambda (x)
  (if-match 0 (_ x) 0)))
(assert-eq (f 1) 1)
