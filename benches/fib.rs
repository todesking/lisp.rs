use criterion::Criterion;
use criterion::{criterion_group, criterion_main};

use lisprs::eval;
use lisprs::list;
use lisprs::parse_all;
use lisprs::GlobalEnv;
use lisprs::Value;

fn run_bench(c: &mut Criterion, name: &str, call: &Value, global: &mut GlobalEnv) {
    c.bench_function(name, |b| {
        b.iter(|| lisprs::eval(&call, global).expect("Error in bench"))
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

fn bench_lambda_nocapture(c: &mut Criterion) {
    let mut global = load_global();
    let n = 1000;
    let call = list![Value::sym("bench-lambda-nocapture"), n];
    let name = call.to_string();
    run_bench(c, &name, &call, &mut global);
}
fn bench_lambda_capture(c: &mut Criterion) {
    let mut global = load_global();
    let n = 1000;
    let call = list![Value::sym("bench-lambda-capture"), n];
    let name = call.to_string();
    run_bench(c, &name, &call, &mut global);
}
fn bench_lambda_letrec(c: &mut Criterion) {
    let mut global = load_global();
    let n = 1000;
    let call = list![Value::sym("bench-lambda-letrec"), n];
    let name = call.to_string();
    run_bench(c, &name, &call, &mut global);
}

criterion_group!(benches_function_call, bench_fib, bench_tak);
criterion_group!(
    benches_lambda,
    bench_lambda_capture,
    bench_lambda_nocapture,
    bench_lambda_letrec
);
criterion_main!(benches_function_call, benches_lambda);
