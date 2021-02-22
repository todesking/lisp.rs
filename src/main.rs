#![cfg(feature = "repl")]

use rustyline::error::ReadlineError;
use rustyline::Editor;

use lisprs::build_top_ast;
use lisprs::eval_top_ast;
use lisprs::GlobalEnv;
use lisprs::Parser;

struct Ctx {
    show_raw_input: bool,
    show_ast: bool,
    global: GlobalEnv,
    parser: Parser,
}

fn main() -> std::io::Result<()> {
    let mut ctx = Ctx {
        show_raw_input: false,
        show_ast: false,
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
    lisprs::eval_str_all_or_panic(include_str!("repl.lisp"), global);
}

fn do_command(line: &str, ctx: &mut Ctx) -> bool {
    match line.trim() {
        ":q" => true,
        "" => false,
        ":show-raw-input" => {
            ctx.show_raw_input = !ctx.show_raw_input;
            println!("set show-raw-input = {}", ctx.show_raw_input);
            false
        }
        ":show-ast" => {
            ctx.show_ast = !ctx.show_ast;
            println!("set show-ast = {}", ctx.show_ast);
            false
        }
        ":ls" => {
            let mut keys = ctx.global.ls().collect::<Vec<_>>();
            keys.sort_unstable();
            for key in keys {
                println!("- [value] {}", key);
            }
            let mut keys = ctx.global.ls_macro().collect::<Vec<_>>();
            keys.sort_unstable();
            for key in keys {
                println!("- [macro] {}", key);
            }
            false
        }
        ":help" => {
            println!("Commands:");
            for cmd in &[":q", ":show-raw-input", ":show-ast", ":ls", ":help"] {
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
            println!("Parse error: {}", err);
        }
        Ok(expr) => {
            if ctx.show_raw_input {
                println!("[Input] {:?}", expr);
            }
            match build_top_ast(&expr, &ctx.global) {
                Err(err) => println!("Compile error: {}", err),
                Ok(ast) => {
                    if ctx.show_ast {
                        println!("AST: {:#?}", ast);
                    }
                    let v = eval_top_ast(&ast, &mut ctx.global);
                    match v {
                        Ok(v) => {
                            println!("     => {}", v);
                        }
                        Err(err) => {
                            println!("Error=> {}", err);
                        }
                    }
                }
            }
        }
    }
    println!("Elapsed: {}[ms]", start.elapsed().as_millis());
}
