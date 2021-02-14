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
