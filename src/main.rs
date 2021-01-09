use io::Write;
use io::{stdin, stdout};
use std::io; // for flush()

mod eval;
mod parser;

use parser::Expr;

fn main() -> io::Result<()> {
    let mut env = std::collections::HashMap::<String, std::rc::Rc<eval::Value>>::new();
    loop {
        print!("LISP.rs> ");
        stdout().flush()?;

        let mut buf = String::new();
        let nread = stdin().read_line(&mut buf)?;
        if nread == 0 {
            // eof
            break;
        }

        if buf == "" {
            continue;
        }
        if buf == ":q" {
            break;
        }

        let expr = buf.parse::<Expr>();
        match expr {
            Err(err) => {
                println!("Parse error: {:?}", err);
            }
            Ok(expr) => {
                println!("[Input] {:?}", expr);
                let v = eval::eval(&(&expr).into(), &mut env);
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
