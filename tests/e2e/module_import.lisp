(module m1
  (:global:define name 'm1)
  (module m11
    (:global:define name 'm11)))

(import-from m1 name)
(:global:assert-eq name 'm1)
(import-from m1:m11 name)
(:global:assert-eq name 'm11)

; lookup priority: current module -> imports
(module m2
 (:global:assert-eq name 'm11)
 (:global:define name 'm2)
 (:global:assert-eq name 'm2))

(module m2
 (:global:assert-eq name 'm2))

(module m2
 (set-global! name 'm2-updated)
 (:global:assert-eq name 'm2-updated))

; set-global! ignores imports
(assert-error
 (lambda () (set-global! name 'global))
 '(VariableNotFound :global:name))

(set-global! :m1:name 'm1-updated)
(:global:assert-eq m1:name 'm1-updated)

(module m3
  (module m33
    (module m333
      (:global:define name 'm333))))
; import module
(import-from m3:m33 m333)
(:global:print-global)
(assert-eq m333:name 'm333)

; import from relative module
(import-from m333 name)
(assert-eq name 'm333)

(module m4
  (:global:define name 'm44)
  (:global:define m4-x 123)
  (module m44
    ; imports are available in nested scope
    (:global:assert-eq name 'm333)
    ; outer-module values are invisivle
    (:global:assert-error
      (lambda () m4-x)
      '(VariableNotFound m4-x))))

(module m5
  (:global:define name 'm5))
(import-from m5 name)
; TODO
; (set-global! name 'm5-updated)
; (:global:assert-eq :m5:name 'm5-updated)
