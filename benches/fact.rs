use criterion::Criterion;
use criterion::{criterion_group, criterion_main};

use lisprs::eval;
use lisprs::global_env::GlobalEnv;
use lisprs::list;
use lisprs::parser::Parser;
use lisprs::value::Value;

fn run_bench(c: &mut Criterion, n: i32, global: &mut GlobalEnv) {
    let call = list![Value::sym("fib"), n];
    c.bench_function(format!("fib({})", n).as_ref(), |b| {
        b.iter(|| lisprs::eval(&call, global))
    });
}

static FIB_SRC: &str = "
(lambda (n)
    (if (eq? n 0) 0
        (if (eq? n 1) 1
            (+ (fib (- n 1)) (fib (- n 2))))))";

fn bench_fib(c: &mut Criterion) {
    let mut parser = Parser::new();
    let mut global = lisprs::predef();
    let fib = eval(&parser.parse(&FIB_SRC).unwrap(), &mut global).unwrap();
    global.set("fib", fib);

    // sanity check
    assert_eq!(
        eval(&list![parser.new_sym("fib"), 6], &mut global),
        Ok(Value::Int(8))
    );

    for n in &[0, 10, 15] {
        run_bench(c, *n, &mut global);
    }
}

criterion_group!(benches, bench_fib);
criterion_main!(benches);
