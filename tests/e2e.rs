use std::fs;
use std::path::Path;

fn run_tests_in(path: &Path) -> Result<(), Box<dyn std::error::Error>> {
    for file in fs::read_dir(path)? {
        let file = file?;
        let name = file
            .path()
            .to_str()
            .expect("file.path().to_str() failed")
            .to_string();
        if name.ends_with(".lisp") {
            run_test(&file.path())?;
        } else {
            run_tests_in(&file.path())?;
        }
    }
    Ok(())
}

fn run_test(path: &Path) -> Result<(), Box<dyn std::error::Error>> {
    let src = fs::read_to_string(path)?;
    let exprs = lisprs::parse_all(src.as_ref())?;

    let mut global = lisprs::predef();
    for expr in exprs {
        lisprs::eval(&expr, &mut global).map_err(|e| {
            println!("Error: {}", expr.to_string());
            println!("=> {}", e.to_string());
            e
        })?;
    }

    Ok(())
}

#[test]
fn test_e2e() -> Result<(), Box<dyn std::error::Error>> {
    run_tests_in(Path::new("test-lisp"))
}
