(__define extract-define-args
 (lambda (args)
   (if-match args
    (((name . args) body . rest)
     `(,name (lambda ,args ,body ,@rest)))
    (if-match args
     ((name expr) `(,name ,expr))
     (error 'syntax-error args)))))

(__defmacro define
  (lambda args
    `(__define ,@(extract-define-args args))))

(__defmacro defmacro
  (lambda args
    `(__defmacro ,@(extract-define-args args))))

(define (cons x y) `(,x . ,y))
(define (car x)
  (if-match x ((x . y) x) (error 'car 'not-cons x)))
(define (cdr x)
  (if-match x ((x . y) y) (error 'cdr 'not-cons x)))

(define (nil? x) (eq? x ()))
(define (map f l)
  (if (nil? l)
    l
    (cons (f (car l)) (map f (cdr l)))))

(defmacro (let defs body . rest)
  ((lambda (defs)
    ((lambda (def-names def-exprs)
      `((lambda (,@def-names) ,body ,@rest) ,@def-exprs))
     (map car defs)
     (map (lambda (l) (car (cdr l))) defs)))
   (map extract-define-args defs)))

(defmacro (define-rec . defs)
  `(begin
    ,@(map
      (lambda (def) `(define ,(car (extract-define-args def)) ())) defs)
    ,@(map
      (lambda (def) `(define . ,(extract-define-args def))) defs)))

(define gensym
  ((lambda (next-id)
    (lambda args
      ((lambda (prefix)
         ((lambda (sym) (set-local! next-id (+ 1 next-id)) sym)
          (make-symbol (str-+ "<gensym-" (to-string prefix) (to-string next-id)">"))))
       (if-match args
        (() "")
        (if-match args
         ((prefix) prefix)
         (error 'gensym 'illegal-argument)))))) 0))

(defmacro (match expr . args)
  (let
    ((the-expr (gensym)))
    (letrec
     (((match-impl args)
       (if-match args
         (((pat expr) . rest) `(if-match ,the-expr (,pat ,expr) ,(match-impl rest)))
         (if (nil? args) `(error 'match-error ,the-expr)
           (error 'match 'illegal-argument args)))))
     `(let ((,the-expr ,expr)) ,(match-impl args)))))
    
(defmacro (and . args)
  (if-match args
    ((a1 . rest) `(if ,a1 (and ,@rest) #f))
    (if (nil? args) #t
      (error 'and 'illegal-argument args))))

(defmacro (or . args)
  (if-match args
    ((a1 . rest) `(if ,a1 #t (or ,@rest)))
    (if (nil? args) #f
      (error 'or 'illegal-argument args))))

(define (not v) (if v #f #t))

(define true #t)
(define false #f)

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
