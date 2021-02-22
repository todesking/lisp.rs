(module m1
  (:global:define x 1)
  (module m1
    (:global:define x 11)))

(:global:assert-eq m1:x 1)
(:global:assert-eq m1:m1:x 11)
(module m1
  (:global:assert-eq x 1)
  (:global:assert-eq :m1:x 1)
  (:global:assert-eq m1:x 11))

(module m1
 (module m1
  (:global:define x 1111)))
(:global:assert-eq m1:m1:x 1111)

(module m2
  (:global:define x 1)
  (module m22
   (:global:define x 2))
  (:global:assert-eq x 1))

