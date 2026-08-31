{
  pkgs,
  pkgsForZ3,
  self',
  venir-toolchain,
  verus-lib,
  ...
}:
let
  inherit (pkgs) lib stdenv mkShell;
  venir = import ./derivation.nix { inherit pkgs self' venir-toolchain; };
  verus-std = import ./verusStd.nix {
    inherit
      pkgs
      self'
      venir-toolchain
      verus-lib
      pkgsForZ3
      ;
  };
in
mkShell {
  packages =
    [
      pkgs.alejandra
      pkgs.mdbook
      pkgsForZ3.z3_4_12
      venir
      self'.legacyPackages.rustToolchain
      verus-std
      pkgs.wrangler
      # pkgs.rustfilt
    ]
    ++ lib.optionals stdenv.isDarwin [
      # `frameworks.CoreServices` used to be here, via
      # `pkgs.darwin.apple_sdk`. That attribute is GONE from nixpkgs -- it was
      # a legacy compatibility stub and its removal is an *evaluation* error,
      # so on darwin this file did not merely build wrong, it did not evaluate
      # at all. Current nixpkgs puts the Apple SDK in the stdenv, so a package
      # that needs a framework no longer names one here.
      pkgs.libiconv
    ];
  shellHook = ''
    export VERUS_Z3_PATH=$(which z3)
    export VARGO_TARGET_DIR="${verus-std}/lib/";
  '';
}
