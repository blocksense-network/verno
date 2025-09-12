use std::collections::HashMap;
use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::{env, fs};

const GIT_COMMIT: &&str = &"GIT_COMMIT";

fn main() -> Result<(), String> {
    // Only use build_data if the environment variable isn't set.
    if env::var(GIT_COMMIT).is_err() {
        build_data::set_GIT_COMMIT()?;
        build_data::set_GIT_DIRTY()?;
        build_data::no_debug_rebuilds()?;
    }

    let out_dir = env::var("OUT_DIR").unwrap();
    let destination = Path::new(&out_dir).join("execute.rs");
    let mut test_file = File::create(destination).unwrap();

    // Try to find the directory that Cargo sets when it is running; otherwise fallback to assuming the CWD
    // is the root of the repository and append the crate path
    let root_dir = match env::var("CARGO_MANIFEST_DIR") {
        Ok(dir) => PathBuf::from(dir).parent().unwrap().to_path_buf(),
        Err(_) => env::current_dir().unwrap(),
    };
    let test_dir = root_dir.join("test_programs");

    // Rebuild if the tests have changed
    println!("cargo:rerun-if-changed=tests");
    // TODO: Running the tests changes the timestamps on test_programs files (file lock?).
    // That has the knock-on effect of then needing to rebuild the tests after running the tests.
    println!(
        "cargo:rerun-if-changed={}",
        test_dir.as_os_str().to_str().unwrap()
    );

    generate_formal_verify_success_tests(&mut test_file, &test_dir);
    generate_formal_verify_failure_tests(&mut test_file, &test_dir);

    Ok(())
}

fn read_test_cases(
    test_data_dir: &Path,
    test_sub_dir: &str,
) -> impl Iterator<Item = (String, PathBuf)> {
    let test_data_dir = test_data_dir.join(test_sub_dir);
    let test_case_dirs = fs::read_dir(test_data_dir)
        .unwrap()
        .flatten()
        .filter(|c| c.path().is_dir());

    test_case_dirs.into_iter().filter_map(|dir| {
        // When switching git branches we might end up with non-empty directories that have a `target`
        // directory inside them but no `Nargo.toml`.
        // These "tests" would always fail, but it's okay to ignore them so we do that here.
        if !dir.path().join("Nargo.toml").exists() {
            return None;
        }

        let test_name = dir
            .file_name()
            .into_string()
            .expect("Directory can't be converted to string");
        if test_name.contains('-') {
            panic!(
                "Invalid test directory: {test_name}. Cannot include `-`, please convert to `_`"
            );
        }
        Some((test_name, dir.path()))
    })
}

/// Tests which must succeed after undergoing formal verification.
fn generate_formal_verify_success_tests(test_file: &mut File, test_data_dir: &Path) {
    let test_type = "formal_verify_success";
    let test_cases = read_test_cases(test_data_dir, test_type);
    for (test_name, test_dir) in test_cases {
        write!(
            test_file,
            r#"
#[test]
fn formal_verify_success_{test_name}() {{
    let test_program_dir = PathBuf::from("{test_dir}");

    let mut cmd = Command::cargo_bin("verno").unwrap();
    cmd.arg("--program-dir").arg(test_program_dir);
    cmd.arg("formal-verify");

    cmd.assert().success();
}}
            "#,
            test_dir = test_dir.display(),
        )
        .expect("Could not write templated test file.");
    }
}

/// Tests which must fail during formal verification.
fn generate_formal_verify_failure_tests(test_file: &mut File, test_data_dir: &Path) {
    let test_type = "formal_verify_failure";
    let test_cases = read_test_cases(test_data_dir, test_type);

    let expected_messages = HashMap::from([("simple_add", vec!["Cannot satisfy constraint"])]);

    for (test_name, test_dir) in test_cases {
        write!(
            test_file,
            r#"
#[test]
fn formal_verify_failure_{test_name}() {{
    let test_program_dir = PathBuf::from("{test_dir}");

    let mut cmd = Command::cargo_bin("verno").unwrap();
    cmd.arg("--program-dir").arg(test_program_dir);
    cmd.arg("formal-verify");

    cmd.assert().failure().stderr(
        predicate::str::contains("The application panicked (crashed).")
        .or(predicate::str::contains("error:")),
    );"#,
            test_dir = test_dir.display(),
        )
        .expect("Could not write templated test file.");

        // Not all tests have expected messages, so match.
        match expected_messages.get(test_name.as_str()) {
            Some(messages) => {
                for message in messages.iter() {
                    write!(
                        test_file,
                        r#"
    cmd.assert().failure().stderr(predicate::str::contains("{message}"));"#
                    )
                    .expect("Could not write templated test file.");
                }
            }
            None => {}
        }

        write!(
            test_file,
            r#"
}}
"#
        )
        .expect("Could not write templated test file.");
    }
}
