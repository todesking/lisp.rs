(define fib (lambda (n)
    (if (eq? n 0) 0
        (if (eq? n 1) 1
            (+ (fib (- n 1)) (fib (- n 2)))))))

(define tak
  (lambda (x y z)
    (if (<= x y)
      y
      (tak
        (tak (- x 1) y z)
        (tak (- y 1) z x)
        (tak (- z 1) x y)))))

(define bench-lambda-nocapture
  (lambda (n)
    (if (eq? n 0)
      ()
      ((lambda ()
        (lambda (x) x)
        (lambda (x) x)
        (lambda (x) x)
        (lambda (x) x)
        (lambda (x) x)
        (lambda (x) x)
        (lambda (x) x)
        (lambda (x) x)
        (lambda (x) x)
        (lambda (x) x)
        (bench-lambda-nocapture (- n 1)))))))

(define bench-lambda-capture
  (lambda (n)
    (if (eq? n 0)
      ()
      ((lambda ()
        (lambda (x) n)
        (lambda (x) n)
        (lambda (x) n)
        (lambda (x) n)
        (lambda (x) n)
        (lambda (x) n)
        (lambda (x) n)
        (lambda (x) n)
        (lambda (x) n)
        (lambda (x) n)
        (bench-lambda-capture (- n 1)))))))

(define bench-lambda-letrec
  (lambda (n)
    (if (eq? n 0)
      ()
      (letrec
        (((f) f))
        f
        f
        f
        f
        f
        f
        f
        f
        f
        f
        (bench-lambda-letrec (- n 1))))))
