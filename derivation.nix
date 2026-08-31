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

  # Build nightly-only features on a stable channel.
  #
  # Not a hack, and not ours: `rust_verify` opens with
  # `#![feature(rustc_private)]` and five more `#![feature]`s, and Verus' own
  # build tool `vargo` sets exactly this variable for exactly this reason.
  # `venir-toolchain.toml` pins a *stable* 1.82.0 with the `rustc-dev`
  # component, and without this the build stops at
  # `error[E0554]: #![feature] may not be used on the stable release channel`.
  # Removing it means moving the pin to a nightly, which changes what the
  # verifier is built against.
  RUSTC_BOOTSTRAP = 1;

  doCheck = false;

  src = fetchFromGitHub {
    owner = "blocksense-network";
    repo = "Venir";
    hash = "sha256-wgP+VkY3wpR+5NIXoFlbIWDU3VQudkwuSdyDX9MUuwU=";
    rev = "15c520be78978cc99ac4ffc799764faa7bcb77b7";
  };

  cargoLock = {
    # Getting the lockfile for a remote project with git dependencies in it is a notoriously difficult problem
    # For now this will work, more idiomatic solutions however are in the works
    lockFile = "${src}/Cargo.lock";

    outputHashes = {
      "getopts-0.2.21" = "sha256-N/QJvyOmLoU5TabrXi8i0a5s23ldeupmBUzP8waVOiU=";
      "smt2parser-0.6.1" = "sha256-AKBq8Ph8D2ucyaBpmDtOypwYie12xVl4gLRxttv5Ods=";
      "air-0.1.0" = "sha256-TeoMUYA4vrBJ7Pn4CuJ3bK9RF/0P/RKgSSBwICpKQnc=";
    };
  };

  # `venir` links against the toolchain's rustc dylibs, so the binary needs an
  # rpath to them. The mechanism is genuinely per-system and is written as one
  # rather than as a platform gate: ELF and Mach-O have different tools and
  # different flags, and the previous unconditional `patchelf` simply does not
  # exist on darwin -- which is why a darwin-built `venir` failed at run time
  # with `Library not loaded: @rpath/librustc_driver-*.dylib` and
  # `no LC_RPATH's found`.
  preFixup =
    if pkgs.stdenv.hostPlatform.isDarwin then
      ''
        install_name_tool -add_rpath "${venir-toolchain}/lib" "$out/bin/${binaryName}"
      ''
    else
      ''
        patchelf --set-rpath "${venir-toolchain}/lib" "$out/bin/${binaryName}"
      '';
}
