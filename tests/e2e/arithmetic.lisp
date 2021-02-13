(define assert-illegal-argument-when-0-args
 (lambda (f)
  (assert-error
    (lambda () (f))
    '(IllegalArgument))))
(define assert-illegal-argument-when-1-args
 (lambda (f)
  (assert-error
    (lambda () (f 1))
    '(IllegalArgument 1))))
(define assert-illegal-argument-when-3-args
 (lambda (f)
  (assert-error
    (lambda () (f 1 2 3))
    '(IllegalArgument 1 2 3))))

(assert-illegal-argument-when-0-args +)
(assert-eq (+ 1) 1)
(assert-eq (+ 1 2) 3)

(assert-illegal-argument-when-0-args -)
(assert-eq (- 1) -1)
(assert-eq (- 3 8) -5)

(assert-illegal-argument-when-0-args *)
(assert-eq (* 2) 2)
(assert-eq (* 2 3) 6)

(assert-illegal-argument-when-0-args /)
(assert-illegal-argument-when-1-args /)
(assert-illegal-argument-when-3-args /)
(assert-eq (/ 5 2) 2)

(assert-illegal-argument-when-0-args %)
(assert-illegal-argument-when-1-args %)
(assert-illegal-argument-when-3-args %)
(assert-eq (% 4 2) 0)
(assert-eq (% 5 2) 1)

(assert-illegal-argument-when-0-args <)
(assert-illegal-argument-when-1-args <)
(assert-eq (< 1 0) false)
(assert-eq (< 1 1) false)
(assert-eq (< 1 2) true)

(assert-illegal-argument-when-0-args <=)
(assert-illegal-argument-when-1-args <=)
(assert-eq (<= 1 0) false)
(assert-eq (<= 1 1) true)
(assert-eq (<= 1 2) true)

(assert-illegal-argument-when-0-args >)
(assert-illegal-argument-when-1-args >)
(assert-eq (> 1 0) true)
(assert-eq (> 1 1) false)
(assert-eq (> 1 2) false)

(assert-illegal-argument-when-0-args >=)
(assert-illegal-argument-when-1-args >=)
(assert-eq (>= 1 0) true)
(assert-eq (>= 1 1) true)
(assert-eq (>= 1 2) false)
