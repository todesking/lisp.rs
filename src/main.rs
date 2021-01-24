#![cfg(feature = "repl")]

use rustyline::error::ReadlineError;
use rustyline::Editor;

use lisprs::global_env::GlobalEnv;
use lisprs::parser::Parser;

struct Ctx {
    show_raw_input: bool,
    global: GlobalEnv,
    parser: Parser,
}

fn main() -> std::io::Result<()> {
    let mut ctx = Ctx {
        show_raw_input: false,
        global: lisprs::predef(),
        parser: Parser::new(),
    };
    load_cli_env(&mut ctx.global);

    let mut rl = Editor::<()>::new();

    println!(":help to show command list");
    loop {
        let line = rl.readline("LISP.rs> ");
        match line {
            Ok(line) => {
                rl.add_history_entry(line.as_str());
                let quit = do_command(&line, &mut ctx);
                if quit {
                    break;
                }
            }
            Err(ReadlineError::Interrupted) | Err(ReadlineError::Eof) => break,
            Err(err) => println!("I/O Error: {:?}", err),
        }
    }
    Ok(())
}

fn load_cli_env(global: &mut GlobalEnv) {
    lisprs::eval_str_or_panic(
        "(define fib (lambda (n)
            (if (eq? n 0) 0
                (if (eq? n 1) 1
                    (+ (fib (- n 1)) (fib (- n 2)))))))",
        global,
    );
}

fn do_command(line: &str, ctx: &mut Ctx) -> bool {
    match line.trim() {
        ":q" => true,
        "" => false,
        ":show_raw_input" => {
            ctx.show_raw_input = !ctx.show_raw_input;
            println!("show_raw_input = {}", ctx.show_raw_input);
            false
        }
        ":ls" => {
            let mut keys = ctx.global.ls().collect::<Vec<_>>();
            keys.sort_unstable();
            for key in keys {
                println!("- {}", key);
            }
            false
        }
        ":help" => {
            println!("Commands:");
            for cmd in &[":q", ":show_raw_input", ":ls", ":help"] {
                println!("- {}", cmd);
            }
            false
        }
        src => {
            read_eval_print(src, ctx);
            false
        }
    }
}

fn read_eval_print(s: &str, ctx: &mut Ctx) {
    let start = std::time::Instant::now();
    let expr = ctx.parser.parse(s);
    match expr {
        Err(err) => {
            println!("Parse error: {:?}", err);
        }
        Ok(expr) => {
            if ctx.show_raw_input {
                println!("[Input] {:?}", expr);
            }
            let v = lisprs::eval(&expr, &mut ctx.global);
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
