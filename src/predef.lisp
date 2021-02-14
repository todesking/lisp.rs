(define list (lambda x x))

(define assert-eq
  (lambda (expected actual)
    (if (eq? expected actual) () (error 'assert-eq expected actual))))

(define assert-error
  (lambda (f err)
    (assert-eq
      (catch-error
        (lambda (err x) (cons err x))
        (f))
      err)))

(define nil? (lambda (x) (eq? x ())))

(define map
  (lambda (f l)
    (if (nil? l)
      l
      (cons (f (car l)) (map f (cdr l))))))

(define gensym
  ((lambda (next-id)
    (lambda args
      ((lambda (prefix)
         ((lambda (sym) (set-local! next-id (+ 1 next-id)) sym)
          (make-symbol (str-+ "<gensym-" prefix ">"))))
       (if-match args
        (() "")
        (if-match args
         ((prefix) prefix)
         (error 'gensym 'illegal-argument)))))) 0))

