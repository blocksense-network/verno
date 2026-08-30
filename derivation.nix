{
  pkgs,
  self',
  venir-toolchain,
  ...
}:
let
  inherit (pkgs) lib rustPlatform fetchFromGitHub;

  customRustPlatform = pkgs.makeRustPlatform {
    cargo = venir-toolchain;
    rustc = venir-toolchain;
  };
in
customRustPlatform.buildRustPackage rec {
  pname = "Venir";
  name = pname;
  binaryName = "venir";
  version = "0.1.0";

  RUSTC_BOOTSTRAP = 1;

  doCheck = false;

  # Moves with Verno rather than independently. `venir` gained a `Counterexample`
  # output line, and Verno's `SmtOutput` refuses any line it does not recognise
  # -- so an old Verno against this `venir` would fail every run. That is
  # deliberate: silently ignoring an unknown output shape is how a producer and a
  # consumer drift apart while both stay green.
  src = fetchFromGitHub {
    owner = "blocksense-network";
    repo = "Venir";
    hash = "sha256-+EEvOhdt555MuYFO4P0upc77Oy1svqpbz2Z+MegRJW0=";
    rev = "7cc0e51d80b2f256ac3d602ec7802c645eb81fb3";
  };

  cargoLock = {
    # Getting the lockfile for a remote project with git dependencies in it is a notoriously difficult problem
    # For now this will work, more idiomatic solutions however are in the works
    lockFile = "${src}/Cargo.lock";

    outputHashes = {
      "getopts-0.2.21" = "sha256-N/QJvyOmLoU5TabrXi8i0a5s23ldeupmBUzP8waVOiU=";
      "smt2parser-0.6.1" = "sha256-AKBq8Ph8D2ucyaBpmDtOypwYie12xVl4gLRxttv5Ods=";
      # `blocksense-network/verus-lib`, not `Aristotelis2002/verus-lib`: the
      # change that stops `air` discarding the solver's model had to live
      # somewhere this project can push to, and a rev pin on an org fork is
      # steadier than a branch pin on a personal one.
      "air-0.1.0" = "sha256-rd2UWJ3fQFfSiWzIOanto8nis8JsmlfUEXrPMSgScq8=";
    };
  };

  preFixup = ''
    patchelf --set-rpath "${venir-toolchain}/lib" "$out/bin/${binaryName}"
  '';
}
