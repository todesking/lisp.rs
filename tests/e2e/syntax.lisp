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
