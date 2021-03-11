{

  description = "LiquidHaskell packages";

  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixos-20.09;

    flake-utils.url = github:numtide/flake-utils;

    liquid-fixpoint.url = github:plredmond/liquid-fixpoint/nix-flake; # TODO change to official repo after merge
    liquid-fixpoint.inputs.nixpkgs.follows = "nixpkgs";
    liquid-fixpoint.inputs.flake-utils.follows = "flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils, liquid-fixpoint }:
    let
      namespaced-outputs = system:
        let
          pkgs = import nixpkgs {
            inherit system;
            overlays = liquid-fixpoint.overlays ++ self.overlays;
          };
        in
        {

          packages = {
            # LH without tests
            liquidhaskell = pkgs.haskellPackages.liquidhaskell;
            ## LH spec/shadow packages
            liquid-base = pkgs.haskellPackages.liquid-base;
            liquid-bytestring = pkgs.haskellPackages.liquid-bytestring;
            liquid-containers = pkgs.haskellPackages.liquid-containers;
            liquid-ghc-prim = pkgs.haskellPackages.liquid-ghc-prim;
            liquid-parallel = pkgs.haskellPackages.liquid-parallel;
            liquid-vector = pkgs.haskellPackages.liquid-vector;
            ## LH bundles
            liquid-platform = pkgs.haskellPackages.liquid-platform;
            liquid-prelude = pkgs.haskellPackages.liquid-prelude;
            ## LH with tests
            liquidhaskell_with_tests = pkgs.haskellPackages.liquidhaskell_with_tests;
          };

          #defaultPackage = pkgs.haskellPackages.liquidhaskell_with_tests;
          defaultPackage = pkgs.haskellPackages.liquidhaskell; # TODO once all packages build, switch to returning the _with_tests version

          devShell = self.defaultPackage.${system}.env;

        };
      unnamespaced-outputs = {

        overlays = [
          # add th-compat to haskellPackages
          (final: prev: {
            haskellPackages = prev.haskellPackages.override {
              overrides = selfH: superH: {
                th-compat = selfH.callHackage "th-compat" "0.1" { };
              };
            };
          })
          # overlay to add our own package
          (import ./overlay.nix)
        ];

      };
    in
    flake-utils.lib.eachDefaultSystem namespaced-outputs // unnamespaced-outputs;
}
