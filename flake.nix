{

  description = "LiquidHaskell packages";

  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixos-22.05;
    flake-utils.url = github:numtide/flake-utils;

    liquid-fixpoint.url = github:plredmond/liquid-fixpoint/nix-flake; # TODO change to official repo after merge
    liquid-fixpoint.inputs.nixpkgs.follows = "nixpkgs";
    liquid-fixpoint.inputs.flake-utils.follows = "flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils, liquid-fixpoint }:
    let
      composeOverlays = funs: builtins.foldl' nixpkgs.lib.composeExtensions (self: super: { }) funs;
      haskellOverlay = compiler: final: prev: new:
        let new-overrides = new.overrides or (a: b: { }); in
        {
          haskell = prev.haskell // {
            packages = prev.haskell.packages // {
              ${compiler} = prev.haskell.packages.${compiler}.override
                (old: old // new // {
                  overrides = self: super: old.overrides self super // new-overrides self super;
                });
            };
          };
        };
      haskellPackagesOverlay = compiler: final: prev: cur-packages-overlay:
        haskellOverlay compiler final prev { overrides = cur-packages-overlay; };
      ghc = "ghc8107"; # Based on https://github.com/ucsd-progsys/liquid-fixpoint/blob/develop/stack.yaml#L3
      beComponent = pkgs: pkg: pkgs.haskell.lib.overrideCabal pkg (old: {
        enableLibraryProfiling = false;
        buildTools = (old.buildTools or [ ]) ++ [ pkgs.z3 ];
      });
      mkOutputs = system:
        let
          # do not use when defining the overlays
          pkgs = import nixpkgs {
            inherit system;
            overlays = [ self.overlay.${system} ];
          };
        in
        {

          packages = {
            # Group 1: LH without tests
            liquidhaskell = pkgs.haskell.packages.${ghc}.liquidhaskell;
            # Group 2: Depends on LH
            liquid-ghc-prim = pkgs.haskell.packages.${ghc}.liquid-ghc-prim;
            # Group 3: Depends on liquid-ghc-prim
            liquid-base = pkgs.haskell.packages.${ghc}.liquid-base;
            # Group 4: Depends on liquid-base
            liquid-bytestring = pkgs.haskell.packages.${ghc}.liquid-bytestring;
            liquid-containers = pkgs.haskell.packages.${ghc}.liquid-containers;
            liquid-parallel = pkgs.haskell.packages.${ghc}.liquid-parallel;
            liquid-platform = pkgs.haskell.packages.${ghc}.liquid-platform;
            liquid-prelude = pkgs.haskell.packages.${ghc}.liquid-prelude;
            liquid-vector = pkgs.haskell.packages.${ghc}.liquid-vector;
            # Group 5: Depends on all of the above
            liquidhaskell_with_tests = pkgs.haskell.packages.${ghc}.liquidhaskell_with_tests;
          };

          defaultPackage = pkgs.haskell.packages.${ghc}.liquidhaskell_with_tests;

          devShell = self.defaultPackage.${system}.env;

          overlay = composeOverlays [
            liquid-fixpoint.overlay.${system}
            self.overlays.${system}.updateAllCabalHashes
            self.overlays.${system}.addLiquidHaskellWithoutTests
            self.overlays.${system}.addLiquidGHCPrim
            self.overlays.${system}.addLiquidBase
            self.overlays.${system}.addLiquidHaskellPackages
            self.overlays.${system}.addLiquidHaskellWithTests
          ];

          overlays = {
            updateAllCabalHashes = final: prev:
              {
                all-cabal-hashes = final.fetchurl {
                  # fetch latest cabal hashes https://github.com/commercialhaskell/all-cabal-hashes/commits/hackage as of Fri May 27 06:40:19 PM UTC 2022
                  url = "https://github.com/commercialhaskell/all-cabal-hashes/archive/91cbef8524376834839ea2814010a0258a06e37e.tar.gz";
                  sha256 = "01h8cd2b1w4060dyyh4zz604gpjyzhvvc0mb1aj18b1z2bcgfakj";
                };
              };
            addLiquidHaskellWithoutTests = final: prev: haskellPackagesOverlay ghc final prev (selfH: superH:
              let callCabal2nix = final.haskell.packages.${ghc}.callCabal2nix; in
              with final.haskell.lib; {
                liquidhaskell =
                  let src = final.nix-gitignore.gitignoreSource [ ".swp" "*.nix" "result" "liquid-*" ] ./.;
                  in
                  dontHaddock # src/Language/Haskell/Liquid/Types/RefType.hs:651:3: error: parse error on input ‘-- | _meetable t1 t2’
                    (doJailbreak # LH requires slightly old versions of recursion-schemes and optparse-applicative
                      (dontCheck (beComponent final (callCabal2nix "liquidhaskell" src { }))));
              });
            addLiquidGHCPrim = final: prev: haskellPackagesOverlay ghc final prev (selfH: superH:
              let callCabal2nix = final.haskell.packages.${ghc}.callCabal2nix; in
              with final.haskell.lib; {
                liquid-ghc-prim = dontHaddock (beComponent final (callCabal2nix "liquid-ghc-prim" ./liquid-ghc-prim { }));
              });
            addLiquidBase = final: prev: haskellPackagesOverlay ghc final prev (selfH: superH:
              let callCabal2nix = final.haskell.packages.${ghc}.callCabal2nix; in
              with final.haskell.lib; {
                liquid-base = dontHaddock (beComponent final (callCabal2nix "liquid-base" ./liquid-base { }));
              });
            addLiquidHaskellPackages = final: prev: haskellPackagesOverlay ghc final prev (selfH: superH:
              let callCabal2nix = final.haskell.packages.${ghc}.callCabal2nix; in
              with final.haskell.lib; {
                liquid-bytestring = (beComponent final (callCabal2nix "liquid-bytestring" ./liquid-bytestring { }));
                liquid-containers = (beComponent final (callCabal2nix "liquid-containers" ./liquid-containers { }));
                liquid-parallel = (beComponent final (callCabal2nix "liquid-parallel" ./liquid-parallel { }));
                liquid-platform = (beComponent final (callCabal2nix "liquid-platform" ./liquid-platform { }));
                liquid-prelude = (beComponent final (callCabal2nix "liquid-prelude" ./liquid-prelude { }));
                liquid-vector = (beComponent final (callCabal2nix "liquid-vector" ./liquid-vector { }));
              });
            addLiquidHaskellWithTests = final: prev: haskellPackagesOverlay ghc final prev (selfH: superH:
              with final.haskell.lib; {
                liquidhaskell_with_tests = overrideCabal selfH.liquidhaskell (old: {
                  doCheck = true; # change the value set above
                  testDepends = old.testDepends or [ ] ++ [ final.hostname ];
                  testHaskellDepends = old.testHaskellDepends ++ builtins.attrValues (builtins.removeAttrs self.packages.${system} [ "liquidhaskell_with_tests" ]);
                  preCheck = ''export TASTY_LIQUID_RUNNER="liquidhaskell -v0"'';
                });
              });
          };

        };
    in
    flake-utils.lib.eachDefaultSystem mkOutputs;
}
