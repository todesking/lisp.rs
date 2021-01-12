use io::Write;
use io::{stdin, stdout};
use std::io; // for flush()

fn main() -> io::Result<()> {
    let mut global = lisprs::predef();
    load_cli_env(&mut global);

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

        if line == "" {
            continue;
        }
        if line == ":q" {
            break;
        }

        let expr = lisprs::parse(line);
        match expr {
            Err(err) => {
                println!("Parse error: {:?}", err);
            }
            Ok(expr) => {
                println!("[Input] {:?}", expr);
                let v = lisprs::eval(&expr, &mut global);
                match v {
                    Ok(v) => {
                        println!("     => {:?}", v);
                    }
                    Err(err) => {
                        println!("Error=> {:?}", err);
                    }
                }
            }
        }
    }
    Ok(())
}

fn load_cli_env(global: &mut lisprs::global_env::GlobalEnv) {
    fn define(global: &mut lisprs::global_env::GlobalEnv, name: &str, src: &str) {
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
