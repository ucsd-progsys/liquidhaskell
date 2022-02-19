{

  description = "LiquidHaskell packages";

  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixos-21.05;

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
        buildTools = old.buildTools or [ ] ++ [ pkgs.z3 ];
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
            # liquidhaskell_with_tests
          };

          defaultPackage = pkgs.haskell.packages.${ghc}.liquidhaskell;

          devShell = self.defaultPackage.${system}.env;

          overlay = composeOverlays [
            liquid-fixpoint.overlay.${system}
            self.overlays.${system}.updateAllCabalHashes
            self.overlays.${system}.addLiquidHaskellWithoutTests
            self.overlays.${system}.addLiquidGHCPrim
            self.overlays.${system}.addLiquidBase
            self.overlays.${system}.addLiquidHaskellPackages
            #self.overlays.${system}.addLiquidHaskellWithTests
          ];

          overlays = {
            updateAllCabalHashes = final: prev:
              {
                all-cabal-hashes = final.fetchurl {
                  # fetch latest cabal hashes https://github.com/commercialhaskell/all-cabal-hashes/commits/hackage as of Thu Feb 17 07:38:07 PM UTC 2022
                  url = "https://github.com/commercialhaskell/all-cabal-hashes/archive/0c6e849a2c97f511653d375f51636b51fc429dc4.tar.gz";
                  sha256 = "0xdnhagd9xj93p3zd6r84x4nr18spwjmhs8dxzq7n199q32snkha";
                };
              };
            addLiquidHaskellWithoutTests = final: prev: haskellPackagesOverlay ghc final prev (selfH: superH:
              let callCabal2nix = prev.haskell.packages.${ghc}.callCabal2nix; in
              with prev.haskell.lib; {
                liquidhaskell =
                  let src = prev.nix-gitignore.gitignoreSource [ "*.nix" "result" "liquid-*" ] ./.;
                  in
                  dontHaddock # src/Language/Haskell/Liquid/Types/RefType.hs:651:3: error: parse error on input ‘-- | _meetable t1 t2’
                    (doJailbreak # LH requires slightly old versions of recursion-schemes and optparse-applicative
                      (dontCheck (beComponent prev (callCabal2nix "liquidhaskell" src { }))));
              });
            addLiquidGHCPrim = final: prev: haskellPackagesOverlay ghc final prev (selfH: superH:
              let callCabal2nix = prev.haskell.packages.${ghc}.callCabal2nix; in
              with prev.haskell.lib; {
                liquid-ghc-prim = dontHaddock (beComponent prev (callCabal2nix "liquid-ghc-prim" ./liquid-ghc-prim { }));
              });
            addLiquidBase = final: prev: haskellPackagesOverlay ghc final prev (selfH: superH:
              let callCabal2nix = prev.haskell.packages.${ghc}.callCabal2nix; in
              with prev.haskell.lib; {
                liquid-base = dontHaddock (beComponent prev (callCabal2nix "liquid-base" ./liquid-base { }));
              });
            addLiquidHaskellPackages = final: prev: haskellPackagesOverlay ghc final prev (selfH: superH:
              let callCabal2nix = prev.haskell.packages.${ghc}.callCabal2nix; in
              with prev.haskell.lib; {
                liquid-bytestring = (beComponent prev (callCabal2nix "liquid-bytestring" ./liquid-bytestring { }));
                liquid-containers = (beComponent prev (callCabal2nix "liquid-containers" ./liquid-containers { }));
                liquid-parallel = (beComponent prev (callCabal2nix "liquid-parallel" ./liquid-parallel { }));
                liquid-platform = (beComponent prev (callCabal2nix "liquid-platform" ./liquid-platform { }));
                liquid-prelude = (beComponent prev (callCabal2nix "liquid-prelude" ./liquid-prelude { }));
                liquid-vector = (beComponent prev (callCabal2nix "liquid-vector" ./liquid-vector { }));
              });
            addLiquidHaskellWithTests = final: prev: haskellPackagesOverlay ghc final prev (selfH: superH:
              with prev.haskell.lib; {
                liquidhaskell_with_tests = overrideCabal selfH.liquidhaskell (old: {
                  doCheck = true; # change the value set above
                  testDepends = old.testDepends or [ ] ++ [ prev.hostname ];
                  testHaskellDepends = old.testHaskellDepends ++ builtins.attrValues (builtins.removeAttrs self.packages.${system} [ "liquidhaskell_with_tests" ]);
                  preCheck = ''export TASTY_LIQUID_RUNNER="liquidhaskell -v0"'';
                });
              });
          };

        };
    in
    flake-utils.lib.eachDefaultSystem mkOutputs;
}
