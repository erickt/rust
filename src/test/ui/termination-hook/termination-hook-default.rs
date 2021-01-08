// run-fail
// error-pattern:"error happened"
// failure-status: 1

#![feature(termination_hook)]
use std::process;

fn main() -> Result<(), &'static str> {
    process::set_termination_hook(Box::new(|err| {
        eprintln!("custom termination hook: {:?}", err);
    }));

    let _ = process::take_termination_hook();

    Err("error happened")
}
