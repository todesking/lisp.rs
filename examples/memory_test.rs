use lisprs::eval;
use lisprs::eval::GlobalEnv;

use lisprs::value::Value;

fn eval_str(global: &mut GlobalEnv, s: &str) -> Value {
    let expr = s.parse().unwrap();
    eval(&expr, global).unwrap()
}

struct Link {
    next: std::cell::RefCell<Option<std::rc::Rc<Link>>>,
}

fn leak() {
    let l = std::rc::Rc::new(Link {
        next: std::cell::RefCell::new(None),
    });
    let mut p = l.next.borrow_mut();
    *p = Some(l.clone());
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if let Some(a1) = args.get(1) {
        // For sanity check
        if a1 == "leak" {
            leak();
        }
    }

    let mut global = lisprs::predef();

    eval_str(
        &mut global,
        "
(define fib (lambda (n)
    (if (eq? n 0) 0
        (if (eq? n 1) 1
            (+ (fib (- n 1)) (fib (- n 2)))))))",
    );
    assert_eq!(eval_str(&mut global, "(fib 6)"), 8.into());

    eval_str(&mut global, "(fib 10)");
    eval_str(
        &mut global,
        "
(define f
    (((lambda (x)
    (lambda (y)
    (lambda (z) (+ x y z)))) 1) 2))",
    );
    assert_eq!(eval_str(&mut global, "(f 3)"), 6.into());
}
