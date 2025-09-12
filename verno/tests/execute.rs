#[allow(unused_imports)]
#[cfg(test)]
mod tests {

    use std::collections::BTreeMap;
    use std::fs;
    use std::io::BufWriter;
    use std::path::{Path, PathBuf};
    use std::process::Command as StdCommand;
    use assert_cmd::prelude::*;
    use predicates::prelude::*;
    use std::process::Command;

    include!(concat!(env!("OUT_DIR"), "/execute.rs"));
}