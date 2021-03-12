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
          (final: prev:
            let
              callCabal2nix = prev.haskellPackages.callCabal2nix;
              source-ignores = [ "*.nix" "result" ];
              source = path: prev.nix-gitignore.gitignoreSource source-ignores path;
            in
            {
              haskellPackages = prev.haskellPackages.override {
                overrides = selfH: superH: with prev.haskell.lib; {
                  # LH without tests
                  liquidhaskell =
                    let src = prev.nix-gitignore.gitignoreSource ([ "liquid-*" ] ++ source-ignores) ./.;
                    in dontCheck (callCabal2nix "liquidhaskell" src { });
                  ## LH spec/shadow packages
                  liquid-base = dontHaddock (callCabal2nix "liquid-base" (source ./liquid-base) { });
                  liquid-bytestring = dontHaddock (callCabal2nix "liquid-bytestring" (source ./liquid-bytestring) { });
                  liquid-containers = (callCabal2nix "liquid-containers" (source ./liquid-containers) { });
                  liquid-ghc-prim = dontHaddock (callCabal2nix "liquid-ghc-prim" (source ./liquid-ghc-prim) { });
                  liquid-parallel = (callCabal2nix "liquid-parallel" (source ./liquid-parallel) { });
                  liquid-vector = (callCabal2nix "liquid-vector" (source ./liquid-vector) { });
                  ## LH bundles
                  liquid-platform = (callCabal2nix "liquid-platform" (source ./liquid-platform) { });
                  liquid-prelude = dontHaddock (callCabal2nix "liquid-prelude" (source ./liquid-prelude) { });
                  ## LH with tests
                  liquidhaskell_with_tests = overrideCabal selfH.liquidhaskell (old: {
                    testDepends = old.testDepends or [ ] ++ [ prev.hostname ];
                    #testHaskellDepends = old.testHaskellDepends ++ projectPackages; # TODO use the packages list somehow
                    preCheck = ''export TASTY_LIQUID_RUNNER="liquidhaskell -v0"'';
                  });
                };
              };
            })
        ];

      };
    in
    flake-utils.lib.eachDefaultSystem namespaced-outputs // unnamespaced-outputs;
}
