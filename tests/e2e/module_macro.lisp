(module m1
  (:global:defmacro (app f . args) `(,f ,@args))
  (:global:define (add x y) (app :global:+ x y))
  (:global:assert-eq (add 1 2) 3)
  )

(assert-eq (:m1:app + 1 2) 3)

(print-global)
(import-from m1 app)
(assert-eq (app + 1 2) 3)
