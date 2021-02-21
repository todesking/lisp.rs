; let
(assert-eq
  (let ((x 1) (y 2))
    (+ x y))
  3)
(assert-eq
  (let ((x 1) (y 2))
    (let ((x 10))
      (+ x y)))
  12)
(assert-eq
  (let ((x 1) (y 2))
    (let ((x 10))
      (set-local! y x)
      (+ x y)))
  20)

(define (f x) (+ x 1))
(assert-eq (f 1) 2)

(assert-eq
  (let (((f x) (+ x x)))
    (f 3))
  6)

(defmacro (my-twice expr) `(+ ,expr ,expr))
(assert-eq (my-twice 123) 246)

(begin
  (define x 1)
  (begin
    (define y 2)
    (define z 3)))
(assert-eq `(,x ,y ,z) '(1 2 3))

(define-rec
  ((even? n) (if (eq? n 0) #t (odd? (- n 1))))
  ((odd? n)  (if (eq? n 0) #f (even? (- n 1)))))
(assert-eq (even? 123) #f)
(assert-eq (odd? 123) #t)

(assert-eq (and #t #t #t #t) #t)
(assert-eq (and #t #t #f #t) #f)
(assert-eq (and) #t)
(define x 1)
(assert-eq (and #f (set-global! x 999)) #f)
(assert-eq x 1)

(assert-eq (or #f #t #f) #t)
(assert-eq (or #f #f #f) #f)
(assert-eq (or) #f)
(define x 1)
(assert-eq (or #t (set-global! x 999)) #t)
(assert-eq x 1)

(assert-eq (not #t) #f)
(assert-eq (not #f) #t)

(define x 0)
(define (inc!) (set-global! x (+ x 1)) x)
(assert-eq
  (match (inc!)
    (99 'a)
    (2 'b)
    (1 'c))
  'c)
(assert-eq x 1)
