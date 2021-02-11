(assert-error
  (lambda () (+))
  '(IllegalArgument))
(assert-eq (+ 1) 1)
(assert-eq (+ 1 2) 3)

(assert-error
  (lambda () (-))
  '(IllegalArgument))
(assert-eq (- 1) -1)
(assert-eq (- 3 8) -5)

(assert-error
  (lambda () (*))
  '(IllegalArgument))
(assert-eq (* 2) 2)
(assert-eq (* 2 3) 6)

(assert-error
  (lambda () (/))
  '(IllegalArgument))
(assert-error
  (lambda () (/ 2))
  '(IllegalArgument 2))
(assert-eq (/ 5 2) 2)

(assert-error
  (lambda () (%))
  '(IllegalArgument))
(assert-error
  (lambda () (% 1))
  '(IllegalArgument 1))
(assert-eq (% 4 2) 0)
(assert-eq (% 5 2) 1)
