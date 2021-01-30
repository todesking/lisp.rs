# Lisp in Rust

Just a toy language.

* Basic syntax:
  * Primitive: `42`, `true`
  * Global variable definition: `(define x 1)`
  * Application: `(f x y)`
  * If: `(if cond then else)`
  * Quote: `'(1 2 3)`
  * Lambda: `(lambda (x y . rest) e1 e2)` / `(lambda rest e1 e2)`
  * Modify local variable: `(set-local! x 1)`(simple value only) / `(unsafe-set-local! x '(1 2 3))`(unlimited and unsafe)
    * Due to reference-counting based memory management, unsafe operations may produce cyclic reference and memor leakage.
* Tail Call Optimization available
* Predefined functions:
  * Basic arithmetic: `+`, `-`, `*`, `/`, `%`
  * Comparing: `eq?`
  * List operations: `cons`, `list`
  * Error handling: `(error value1 value2)`(Raise user error), `(catch-error (lambda (error-kind values) ...) expr)`(Catch error in expr)

## Usage

`cargo run --release` to run REPL.

```
LISP.rs> (define make-counter (lambda () ((lambda (x) (lambda () (set-local! x (+ 1 x)) x)) 0)))
     => ()
LISP.rs> (define counter-1 (make-counter))
     => ()
LISP.rs> (define counter-2 (make-counter))
     => ()
LISP.rs> (counter-1)
     => 1
LISP.rs> (counter-1)
     => 2
LISP.rs> (counter-2)
     => 1
LISP.rs> (counter-1)
     => 3
LISP.rs> (counter-2)
     => 2
LISP.rs> (fib 30) ; predefined function
     => 832040
Elapsed: 4208[ms]
```

Predefined `fib` definition:
```
(define fib (lambda (n)
    (if (eq? n 0) 0
        (if (eq? n 1) 1
            (+ (fib (- n 1)) (fib (- n 2)))))))
```
