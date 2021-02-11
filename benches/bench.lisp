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
