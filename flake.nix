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
      composeOverlays = funs: builtins.foldl' nixpkgs.lib.composeExtensions (self: super: { }) funs;
      mkOutputs = system:
        let
          pkgs = import nixpkgs {
            inherit system;
            overlays = [ self.overlay.${system} ];
          };
        in
        {

          packages = {
            # Group 1: LH without tests
            liquidhaskell = pkgs.haskellPackages.liquidhaskell;
            # Group 2: Depends on LH
            liquid-ghc-prim = pkgs.haskellPackages.liquid-ghc-prim;
            # Group 3: Depends on liquid-ghc-prim
            liquid-base = pkgs.haskellPackages.liquid-base;
            # Group 4: Depends on liquid-base
            liquid-bytestring = pkgs.haskellPackages.liquid-bytestring;
            liquid-containers = pkgs.haskellPackages.liquid-containers;
            liquid-parallel = pkgs.haskellPackages.liquid-parallel;
            liquid-platform = pkgs.haskellPackages.liquid-platform;
            liquid-prelude = pkgs.haskellPackages.liquid-prelude;
            liquid-vector = pkgs.haskellPackages.liquid-vector;
            # Group 5: Depends on all of the above
            # liquidhaskell_with_tests
          };

          defaultPackage = pkgs.haskellPackages.liquidhaskell_with_tests;

          devShell = pkgs.haskellPackages.liquidhaskell.env;

          overlay = composeOverlays [
            liquid-fixpoint.overlay.${system}
            self.overlays.${system}.addTHCompat
            self.overlays.${system}.addLiquidHaskellWithoutTests
            self.overlays.${system}.addLiquidGHCPrim
            self.overlays.${system}.addLiquidBase
            self.overlays.${system}.addLiquidHaskellPackages
            self.overlays.${system}.addLiquidHaskellWithTests
          ];

          overlays = {
            addTHCompat = final: prev: {
              haskellPackages = prev.haskellPackages.extend (selfH: superH: {
                th-compat = selfH.callHackage "th-compat" "0.1" { };
              });
            };
            addLiquidHaskellWithoutTests = final: prev: {
              haskellPackages = prev.haskellPackages.extend (selfH: superH: with prev.haskell.lib; {
                ## LH without tests
                liquidhaskell =
                  let src = prev.nix-gitignore.gitignoreSource [ "*.nix" "result" "liquid-*" ] ./.;
                  in dontCheck (disableLibraryProfiling (prev.haskellPackages.callCabal2nix "liquidhaskell" src { }));
              });
            };
            addLiquidGHCPrim = final: prev: {
              haskellPackages = prev.haskellPackages.extend (selfH: superH: with prev.haskell.lib; {
                liquid-ghc-prim = dontHaddock (prev.haskellPackages.callCabal2nix "liquid-ghc-prim" ./liquid-ghc-prim { });
              });
            };
            addLiquidBase = final: prev: {
              haskellPackages = prev.haskellPackages.extend (selfH: superH: with prev.haskell.lib; {
                liquid-base = dontHaddock (prev.haskellPackages.callCabal2nix "liquid-base" ./liquid-base { });
              });
            };
            addLiquidHaskellPackages = final: prev:
              let callCabal2nix = prev.haskellPackages.callCabal2nix; in
              {
                haskellPackages = prev.haskellPackages.extend (selfH: superH: with prev.haskell.lib; {
                  liquid-bytestring = dontHaddock (callCabal2nix "liquid-bytestring" ./liquid-bytestring { });
                  liquid-containers = (callCabal2nix "liquid-containers" ./liquid-containers { });
                  liquid-parallel = (callCabal2nix "liquid-parallel" ./liquid-parallel { });
                  liquid-platform = (callCabal2nix "liquid-platform" ./liquid-platform { });
                  liquid-prelude = dontHaddock (callCabal2nix "liquid-prelude" ./liquid-prelude { });
                  liquid-vector = (callCabal2nix "liquid-vector" ./liquid-vector { });
                });
              };
            addLiquidHaskellWithTests = final: prev: {
              haskellPackages = prev.haskellPackages.extend (selfH: superH: with prev.haskell.lib; {
                liquidhaskell_with_tests = overrideCabal selfH.liquidhaskell (old: {
                  doCheck = true;
                  testDepends = old.testDepends or [ ] ++ [ prev.hostname ];
                  testHaskellDepends = old.testHaskellDepends ++ builtins.attrValues self.packages.${system};
                  preCheck = ''export TASTY_LIQUID_RUNNER="liquidhaskell -v0"'';
                });
              });
            };
          };

        };
    in
    flake-utils.lib.eachDefaultSystem mkOutputs;
}
