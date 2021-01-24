use io::Write;
use io::{stdin, stdout};
use std::io; // for flush()

use lisprs::global_env::GlobalEnv;
use lisprs::parser::Parser;

struct Ctx {
    show_raw_input: bool,
}

fn main() -> io::Result<()> {
    let mut parser = Parser::new();
    let mut global = lisprs::predef();
    load_cli_env(&mut global);

    let mut ctx = Ctx {
        show_raw_input: false,
    };

    loop {
        print!("LISP.rs> ");
        stdout().flush()?;

        let mut line = String::new();
        let nread = stdin().read_line(&mut line)?;
        if nread == 0 {
            // eof
            break;
        }
        let line = line.trim();

        match line.trim() {
            ":q" => break,
            "" => {}
            ":show_raw_input" => {
                ctx.show_raw_input = !ctx.show_raw_input;
                println!("show_raw_input = {}", ctx.show_raw_input);
            }
            src => read_eval_print(src, &mut parser, &mut global, &ctx),
        }
    }
    Ok(())
}

fn load_cli_env(global: &mut GlobalEnv) {
    fn define(global: &mut GlobalEnv, name: &str, src: &str) {
        let expr = lisprs::parse(src).expect(name);
        let value = lisprs::eval(&expr, global).expect(name);
        global.set(name, value);
    }
    define(
        global,
        "fib",
        "
        (lambda (n)
            (if (eq? n 0) 0
                (if (eq? n 1) 1
                    (+ (fib (- n 1)) (fib (- n 2))))))",
    );
}

fn read_eval_print(s: &str, parser: &mut Parser, global: &mut GlobalEnv, ctx: &Ctx) {
    let start = std::time::Instant::now();
    let expr = parser.parse(s);
    match expr {
        Err(err) => {
            println!("Parse error: {:?}", err);
        }
        Ok(expr) => {
            if ctx.show_raw_input {
                println!("[Input] {:?}", expr);
            }
            let v = lisprs::eval(&expr, global);
            match v {
                Ok(v) => {
                    println!("     => {}", v);
                }
                Err(err) => {
                    println!("Error=> {:?}", err);
                }
            }
        }
    }
    println!("Elapsed: {}[ms]", start.elapsed().as_millis());
}
