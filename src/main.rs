use io::Write;
use io::{stdin, stdout};
use std::io; // for flush()

mod parser;
mod engine;

use parser::Expr;


fn main() -> io::Result<()> {
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

        let e = buf.parse::<Expr>();
        println!("=> {:?}", e);
    }
    Ok(())
}
