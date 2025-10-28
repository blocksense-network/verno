#[allow(unused_imports)]
#[cfg(test)]
mod tests {

    use assert_cmd::prelude::*;
    use predicates::prelude::*;
    use std::collections::BTreeMap;
    use std::fs;
    use std::io::BufWriter;
    use std::path::{Path, PathBuf};
    use std::process::Command as StdCommand;
    use std::process::Command;

    include!(concat!(env!("OUT_DIR"), "/execute.rs"));

    #[test]
    fn formal_verify_library_file_verifies_all_functions() {
        let test_program_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("workspace root")
            .join("test_programs/formal_verify_file_mode/library_module");
        let noir_file = test_program_dir.join("src/lib.nr");

        let mut cmd = Command::cargo_bin("verno").unwrap();
        cmd.arg("--program-dir").arg(&test_program_dir);
        cmd.arg("formal-verify");
        cmd.arg(&noir_file);

        cmd.assert()
            .success()
            .stdout(
                predicate::str::contains("Verifying `square`")
                    .and(predicate::str::contains("Verifying `increment`")),
            )
            .stdout(predicate::str::contains("Verification successful!"));
    }

    #[test]
    fn formal_verify_library_without_file_errors() {
        let test_program_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("workspace root")
            .join("test_programs/formal_verify_file_mode/library_module");

        let mut cmd = Command::cargo_bin("verno").unwrap();
        cmd.arg("--program-dir").arg(&test_program_dir);
        cmd.arg("formal-verify");

        cmd.assert().failure().stderr(predicate::str::contains(
            "no binary packages with a `main` function were found",
        ));
    }

    #[test]
    fn formal_verify_cross_file_only_targets_source_file() {
        let package_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("workspace root")
            .join("test_programs/formal_verify_file_mode/cross_file");
        let noir_file = package_dir.join("src/lib.nr");

        let mut cmd = Command::cargo_bin("verno").unwrap();
        cmd.arg("--program-dir").arg(&package_dir);
        cmd.arg("formal-verify").arg(&noir_file);

        cmd.assert()
            .success()
            .stdout(predicate::str::contains("Verifying `apply_double`"))
            .stdout(predicate::str::contains("Verifying `double`").not())
            .stdout(predicate::str::contains("Verification successful!"));
    }

    #[test]
    fn formal_verify_cross_file_verifies_helper_when_requested() {
        let package_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("workspace root")
            .join("test_programs/formal_verify_file_mode/cross_file");
        let noir_file = package_dir.join("src/helpers.nr");

        let mut cmd = Command::cargo_bin("verno").unwrap();
        cmd.arg("--program-dir").arg(&package_dir);
        cmd.arg("formal-verify").arg(&noir_file);

        cmd.assert()
            .success()
            .stdout(predicate::str::contains("Verifying `helpers::double`"))
            .stdout(predicate::str::contains("Verification successful!"));
    }
}
