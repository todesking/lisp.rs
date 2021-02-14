(define even? ())
(define odd? ())

(letrec
  (((even? x) (if (eq? x 0) true (odd? (- x 1))))
   ((odd? x) (if (eq? x 0) false (even? (- x 1)))))
  (set-global! even? even?)
  (set-global! odd? odd?))

(assert-eq (even? 0) true)
(assert-eq (odd? 0) false)

(assert-eq (even? 10) true)
(assert-eq (odd? 10) false)

(assert-eq (even? 9) false)
(assert-eq (odd? 9) true)

(define f
  (lambda (x)
   (letrec (((get-g) g)
            ((g x) (+ x 1)))
    (lambda (y)
      (get-g)))))

(assert-eq
 (((f 1) 2) 3)
 4)

(assert-eq
 (let ((x 1))
  (letrec
   (((f y)
     (if-match 1
      (1 (+ x y)) #f)))
   (f 123)))
 124)
