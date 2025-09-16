use std::env;
use std::ffi::OsString;
use std::process::{Command, exit};

fn find_nargo_binary() -> Option<OsString> {
    // 1. Check NARGO_PATH environment variable
    if let Ok(nargo_path) = env::var("NARGO_PATH") {
        let path: OsString = nargo_path.into();
        if std::path::Path::new(&path).exists() {
            return Some(path);
        }
    }

    // 2. Check next to the current executable
    if let Ok(current_exe) = env::current_exe() {
        if let Some(dir) = current_exe.parent() {
            let nargo_path = dir.join("nargo");
            if nargo_path.exists() {
                return Some(nargo_path.into());
            }
        }
    }

    // 3. Check the PATH
    if let Ok(path_var) = env::var("PATH") {
        for path_entry in env::split_paths(&path_var) {
            let nargo_path = path_entry.join("nargo");
            if nargo_path.exists() {
                return Some(nargo_path.into());
            }
        }
    }

    None
}

pub fn proxy_to_nargo(args: &Vec<OsString>) {
    if let Some(nargo_binary) = find_nargo_binary() {
        let status =
            Command::new(nargo_binary).args(args).status().expect("Failed to execute nargo.");

        exit(status.code().unwrap_or(1));
    } else {
        eprintln!("Error: nargo not found.");
        eprintln!(
            "To run normal Noir commands, you need to have 'nargo' installed and in your PATH."
        );
        eprintln!(
            "Alternatively, you can set the NARGO_PATH environment variable to the full path of the nargo binary."
        );
        exit(1);
    }
}
