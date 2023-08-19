use std::io;
use serde::{Deserialize, Serialize};

mod domain;
use domain::Domain as Domain;

mod extract;
use extract::Minimization as Minimization;
use extract::Minimization as Step;

// Taken from https://github.com/opencompl/egg-tactic-code

#[derive(Deserialize, Debug)]
#[serde(tag = "request")]
enum Request {
    PerformRewrite {
        domains : Vec<(String, Domain)>,
        target : Minimization,
    }
}

#[derive(Serialize, Debug)]
#[serde(tag = "response")]
enum Response {
    Success { steps: Vec<Step> },
    Error { error: String }
}

fn main_json() -> io::Result<()> {
    env_logger::init();
    let stdin = io::stdin();
    let mut stdout = io::stdout();
    let deserializer = 
        serde_json::Deserializer::from_reader(stdin.lock());

    for read in deserializer.into_iter() {
        let response = match read {
            Err(err) => Response::Error {
                error: format!("Deserialization error: {}", err),
            },
            Ok(req) => {
                match req {
                    Request::PerformRewrite 
                        { domains, target } => 
                    Response::Success {
                        steps: get_steps(target, domains, false)
                    }
                }
            }
        };

        serde_json::to_writer_pretty(&mut stdout, &response)?;
        println!()
    }

    Ok(())
}

fn main() {
    main_json().unwrap();
}
