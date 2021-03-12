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
      haskellPackagesOverlay = compiler: final: prev: overrides: {
        haskell = prev.haskell // {
          packages = prev.haskell.packages // {
            ${compiler} = prev.haskell.packages.${compiler}.extend overrides;
          };
        };
      };
      ghc = "ghc8102";
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

          defaultPackage = pkgs.haskell.packages.${ghc}.liquidhaskell_with_tests;

          devShell = pkgs.haskell.packages.${ghc}.liquidhaskell.env;

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
            addTHCompat = final: prev: haskellPackagesOverlay ghc final prev (selfH: superH: {
              th-compat = selfH.callHackage "th-compat" "0.1" { };
            });
            addLiquidHaskellWithoutTests = final: prev: haskellPackagesOverlay ghc final prev (selfH: superH:
              let callCabal2nix = prev.haskell.packages.${ghc}.callCabal2nix; in
              with prev.haskell.lib; {
                liquidhaskell =
                  let src = prev.nix-gitignore.gitignoreSource [ "*.nix" "result" "liquid-*" ] ./.;
                  in dontCheck (disableLibraryProfiling (callCabal2nix "liquidhaskell" src { }));
              });
            addLiquidGHCPrim = final: prev: haskellPackagesOverlay ghc final prev (selfH: superH:
              let callCabal2nix = prev.haskell.packages.${ghc}.callCabal2nix; in
              with prev.haskell.lib; {
                liquid-ghc-prim = dontHaddock (callCabal2nix "liquid-ghc-prim" ./liquid-ghc-prim { });
              });
            addLiquidBase = final: prev: haskellPackagesOverlay ghc final prev (selfH: superH:
              let callCabal2nix = prev.haskell.packages.${ghc}.callCabal2nix; in
              with prev.haskell.lib; {
                liquid-base = dontHaddock (callCabal2nix "liquid-base" ./liquid-base { });
              });
            addLiquidHaskellPackages = final: prev: haskellPackagesOverlay ghc final prev (selfH: superH:
              let callCabal2nix = prev.haskell.packages.${ghc}.callCabal2nix; in
              with prev.haskell.lib; {
                liquid-bytestring = dontHaddock (callCabal2nix "liquid-bytestring" ./liquid-bytestring { });
                liquid-containers = (callCabal2nix "liquid-containers" ./liquid-containers { });
                liquid-parallel = (callCabal2nix "liquid-parallel" ./liquid-parallel { });
                liquid-platform = (callCabal2nix "liquid-platform" ./liquid-platform { });
                liquid-prelude = dontHaddock (callCabal2nix "liquid-prelude" ./liquid-prelude { });
                liquid-vector = (callCabal2nix "liquid-vector" ./liquid-vector { });
              });
            addLiquidHaskellWithTests = final: prev: haskellPackagesOverlay ghc final prev (selfH: superH:
              with prev.haskell.lib; {
                liquidhaskell_with_tests = overrideCabal selfH.liquidhaskell (old: {
                  doCheck = true;
                  testDepends = old.testDepends or [ ] ++ [ prev.hostname ];
                  testHaskellDepends = old.testHaskellDepends ++ builtins.attrValues self.packages.${system};
                  preCheck = ''export TASTY_LIQUID_RUNNER="liquidhaskell -v0"'';
                });
              });
          };

        };
    in
    flake-utils.lib.eachDefaultSystem mkOutputs;
}
