use criterion::Criterion;
use criterion::{criterion_group, criterion_main};

use lisprs::eval;
use lisprs::parse_all;
use lisprs::eval::GlobalEnv;
use lisprs::list;
use lisprs::value::Value;

fn run_bench(c: &mut Criterion, name: &str, call: &Value, global: &mut GlobalEnv) {
    c.bench_function(name, |b| {
        b.iter(|| lisprs::eval(&call, global))
    });
}

fn load_global() -> GlobalEnv {
    let mut global = lisprs::predef();
    let bench_src = include_str!("bench.lisp");
    for expr in parse_all(bench_src).expect("Parse error at bench.lisp") {
        eval(&expr, &mut global).expect("Eval error at bench.lisp");
    }
    global
}

fn bench_fib(c: &mut Criterion) {
    let mut global = load_global();
    // sanity check
    assert_eq!(
        eval(&list![Value::sym("fib"), 6], &mut global),
        Ok(Value::Int(8))
    );

    for n in &[15] {
    let call = list![Value::sym("fib"), n];
    let name = format!("fib({})", n);
        run_bench(c, &name, &call, &mut global);
    }
}

fn bench_tak(c: &mut Criterion) {
    let mut global = load_global();
    // sanity check
    assert_eq!(
        eval(&list![Value::sym("tak"), 0, 1, 2], &mut global),
        Ok(Value::Int(1))
    );
    let (x, y, z) = (8, 3, 0);
    let name = format!("tak({}, {}, {})", x, y, z);
    let call = list![Value::sym("tak"), x, y, z];
    run_bench(c, &name, &call, &mut global);
}


criterion_group!(benches, bench_fib, bench_tak);
criterion_main!(benches);
