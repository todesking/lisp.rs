(module m1
  (:global:define name 'm1)
  (:global:define (f) name))

(module m2
  (:global:define name 'm2))
(module m2
  (:global:define (f) name))

(module m1
  (:global:assert-eq (f) 'm1))

(module m2
  (:global:assert-eq (f) 'm2))

(:global:assert-error
  (lambda () (f))
  '(VariableNotFound f))

(:global:define name 'global)
(:global:define (f) name)

(:global:assert-eq (f) 'global)
(:global:assert-eq (:global:f) 'global)
(:global:assert-eq (:m1:f) 'm1)
(:global:assert-eq (:m2:f) 'm2)
