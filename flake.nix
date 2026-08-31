{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    nixpkgs-for-z3.url = "github:NixOS/nixpkgs/c792c60b8a97daa7efe41a6e4954497ae410e0c1";
    flake-parts.url = "github:hercules-ci/flake-parts";
    fenix = {
      url = "github:nix-community/fenix";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    verus-lib = {
      url = "github:Aristotelis2002/verus-lib?ref=synced_main";
      flake = false;
    };
  };

  outputs =
    inputs@{
      nixpkgs,
      nixpkgs-for-z3,
      flake-parts,
      fenix,
      verus-lib,
      ...
    }:
    let
      # The `venir` toolchain, resolved PER SYSTEM.
      #
      # This used to be a single `system = "x86_64-linux";` binding in this
      # `let`, outside `perSystem` -- so all four systems listed below were
      # handed a toolchain built for x86_64-linux. That is the whole of why
      # `venir` has been recorded as Linux-only since 2026-08-28: it is not.
      # `venir-toolchain.toml` names a channel and **no host**, and on
      # aarch64-darwin `venir` builds in 30.5 s and runs the full Noir proof
      # corpus at 121 proved / 12 not-proved in 78 s (measured 2026-08-31).
      #
      # The `sha256` stays a single literal and that is correct, not an
      # oversight: `fromToolchainFile` hashes the *channel manifest*
      # (`channel-rust-1.82.0.toml`), which is one file for every platform.
      # Measured -- asking fenix for the aarch64-darwin toolchain with a
      # deliberately wrong hash reports the identical value already pinned
      # here. Per-platform component tarballs are fetched underneath it with
      # their own hashes, from that manifest.
      toolchainFor =
        system:
        fenix.packages.${system}.fromToolchainFile {
          file = ./venir-toolchain.toml;
          sha256 = "sha256-yMuSb5eQPO/bHv+Bcf/US8LVMbf/G/0MSfiPwBhiPpk=";
        };
    in
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      perSystem =
        {
          pkgs,
          inputs',
          self',
          system,
          ...
        }:
        let
          venir-toolchain = toolchainFor system;
        in
        {
          legacyPackages.rustToolchain =
            with inputs'.fenix.packages;
            with stable;
            combine [
              cargo
              clippy
              rust-analyzer
              rust-src
              rustc
              rustfmt
            ];
          devShells.default = import ./shell.nix {
            inherit
              pkgs
              self'
              venir-toolchain
              verus-lib
              ;
            pkgsForZ3 = inputs'.nixpkgs-for-z3.legacyPackages;
          };
        };
    };
}
