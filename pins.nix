{ config ? {}, ... }:
let
  nixpkgs = import (
    builtins.fetchTarball {
      # fetch latest nixpkgs https://github.com/NixOS/nixpkgs-channels/tree/nixos-20.03 as of Fri 04 Sep 2020 11:43:55 PM UTC
      url = "https://github.com/NixOS/nixpkgs-channels/archive/5607e74b1dd2c9bf19fcb35ddf5ee68b3228f67c.tar.gz";
      sha256 = "1glq1gsbq7n8564w798aa37j2v7xyn2baawfdrg9gi8ll4fbyajl";
    }
  ) { inherit config; };
  # liquidhaskell plugin requires ghc 8.10.1
  haskellCompilerPackages = nixpkgs.haskell.packages."ghc8101";
  # override dependencies in nixpkgs
  haskellPackages = haskellCompilerPackages.override (
    old: {
      all-cabal-hashes = nixpkgs.fetchurl {
        # fetch latest cabal hashes https://github.com/commercialhaskell/all-cabal-hashes/tree/hackage as of Fri 04 Sep 2020 11:43:55 PM UTC
        url = "https://github.com/commercialhaskell/all-cabal-hashes/archive/e8c1a5421b098eb15defb7573cfce04f7fa71c54.tar.gz";
        sha256 = "1hh3saqwwr91qj1qkik7i6np1jbvq6r29vcd615bb0hg1glxaprq";
      };
      overrides = self: super: with nixpkgs.haskell.lib; rec {
        # turn off tests and haddocks and version bounds by default
        mkDerivation = args: super.mkDerivation (
          args // {
            doCheck = false;
            doHaddock = false;
            jailbreak = true;
          }
        );
        # declare each of the packages contained in this repo
        ## LH support packages
        liquid-fixpoint = overrideCabal (self.callCabal2nix "liquid-fixpoint" (nixpkgs.nix-gitignore.gitignoreSource [] ./liquid-fixpoint) {}) (old: withZ3 old { doCheck = true; doHaddock = true; preCheck = ''export PATH="$PWD/dist/build/fixpoint:$PATH"''; });
        liquidhaskell = overrideCabal (self.callCabal2nix "liquidhaskell" (nixpkgs.nix-gitignore.gitignoreSource [] ./.) {}) (old: withZ3 old { doCheck = true; doHaddock = true; preCheck = "export TASTY_LIQUID_RUNNER='./dist/build/liquid/liquid'"; });
        ## LH spec packages
        liquid-base = overrideCabal (self.callCabal2nix "liquid-base" ./liquid-base {}) (old: withZ3 old { doCheck = true; });
        liquid-bytestring = overrideCabal (self.callCabal2nix "liquid-bytestring" ./liquid-bytestring {}) (old: withZ3 old { doCheck = true; });
        liquid-containers = overrideCabal (self.callCabal2nix "liquid-containers" ./liquid-containers {}) (old: withZ3 old { doCheck = true; doHaddock = true; });
        liquid-ghc-prim = overrideCabal (self.callCabal2nix "liquid-ghc-prim" ./liquid-ghc-prim {}) (old: withZ3 old { doCheck = true; });
        liquid-prelude = overrideCabal (self.callCabal2nix "liquid-prelude" ./liquid-prelude {}) (old: withZ3 old { doCheck = true; });
        liquid-vector = overrideCabal (self.callCabal2nix "liquid-vector" ./liquid-vector {}) (old: withZ3 old { doCheck = true; doHaddock = true; });
        ## LH bundles
        liquid-parallel = overrideCabal (self.callCabal2nix "liquid-parallel" ./liquid-parallel {}) (old: withZ3 old { doCheck = true; doHaddock = true; });
        liquid-platform = overrideCabal (self.callCabal2nix "liquid-platform" ./liquid-platform {}) (old: { doCheck = true; doHaddock = true; });
        # declare dependencies using the latest hackage releases as of Thu 27 Aug 2020 04:08:52 PM UTC
        hashable = self.callHackage "hashable" "1.3.0.0" {}; # ouch; requires recompilation of around 30 packages
        optics = self.callHackage "optics" "0.3" {};
        optics-core = self.callHackage "optics-core" "0.3.0.1" {};
        optics-extra = self.callHackage "optics-extra" "0.3" {};
        optics-th = self.callHackage "optics-th" "0.3.0.2" {};
        # declare test-dependencies using the latest hackage releases as of Thu 27 Aug 2020 04:08:52 PM UTC
        memory = self.callHackage "memory" "0.15.0" {};
        git = overrideCabal (self.callHackage "git" "0.3.0" {}) (old: { patches = [ ./git-0.3.0_fix-monad-fail-for-ghc-8.10.1.patch ]; });
      };
    }
  );
  # helper to include z3 during build and test of a package
  withZ3 = old: new: new // { buildTools = old.buildTools or [] ++ [ nixpkgs.z3 ]; };
  #
  projectPackages = with haskellPackages; [
    liquid-base
    liquid-bytestring
    liquid-containers
    liquid-fixpoint
    liquid-ghc-prim
    liquid-parallel
    liquid-platform
    liquid-prelude
    liquid-vector
    liquidhaskell
  ];
in
{
  inherit nixpkgs;
  inherit haskellPackages;
  inherit projectPackages;
}
