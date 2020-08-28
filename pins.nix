{ config ? {}, ... }:
let
  nixpkgs = import (
    builtins.fetchTarball {
      # fetch latest nixpkgs https://github.com/NixOS/nixpkgs-channels/tree/nixos-20.03 as of Thu 27 Aug 2020 04:08:52 PM UTC
      url = "https://github.com/NixOS/nixpkgs-channels/archive/feff2fa6659799fe7439038b3eba453d62a16e69.tar.gz";
      sha256 = "0vlnrwlxl6xf6b8rmiy7as2lhi015nklyj2xdiy3ly8xznq69ll9";
    }
  ) { inherit config; };
  # liquidhaskell plugin requires ghc 8.10.1
  haskellCompilerPackages = nixpkgs.haskell.packages."ghc8101";
  # override dependencies in nixpkgs
  haskellPackages = haskellCompilerPackages.override (
    old: {
      all-cabal-hashes = nixpkgs.fetchurl {
        # fetch latest cabal hashes https://github.com/commercialhaskell/all-cabal-hashes/tree/hackage as of Thu 27 Aug 2020 04:08:52 PM UTC
        url = "https://github.com/commercialhaskell/all-cabal-hashes/archive/2f5cbba0f21b2be91d0fc2a9d303525a09c6129d.tar.gz";
        sha256 = "1q44anb5wfngpmhhphs32iviygn8khbp7qvw893ss6sd8pgf8pbg";
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
        liquid-base = lhComponent (self.callCabal2nix "liquid-base" ./liquid-base {});
        liquid-bytestring = lhComponent (self.callCabal2nix "liquid-bytestring" ./liquid-bytestring {});
        liquid-containers = lhComponent (self.callCabal2nix "liquid-containers" ./liquid-containers {});
        liquid-fixpoint = lhComponent (self.callCabal2nix "liquid-fixpoint" (nixpkgs.nix-gitignore.gitignoreSource [] ./liquid-fixpoint) {});
        liquid-ghc-prim = lhComponent (self.callCabal2nix "liquid-ghc-prim" ./liquid-ghc-prim {});
        liquid-parallel = lhComponent (self.callCabal2nix "liquid-parallel" ./liquid-parallel {});
        liquid-platform = lhComponent (self.callCabal2nix "liquid-platform" ./liquid-platform {});
        liquid-prelude = lhComponent (self.callCabal2nix "liquid-prelude" ./liquid-prelude {});
        liquid-vector = lhComponent (self.callCabal2nix "liquid-vector" ./liquid-vector {});
        liquidhaskell = lhComponent (self.callCabal2nix "liquidhaskell" (nixpkgs.nix-gitignore.gitignoreSource [] ./.) {});
        # declare dependencies using the latest hackage releases as of Thu 27 Aug 2020 04:08:52 PM UTC
        hashable = self.callHackage "hashable" "1.3.0.0" {}; # ouch; requires recompilation of around 30 packages
        optics = self.callHackage "optics" "0.3" {};
        optics-core = self.callHackage "optics-core" "0.3.0.1" {};
        optics-extra = self.callHackage "optics-extra" "0.3" {};
        optics-th = self.callHackage "optics-th" "0.3.0.2" {};
        #memory = self.callHackage "memory" "0.15.0" {};
        #tls = self.callHackage "tls" "1.5.4" {};
      };
    }
  );
  # define a function to turn on tests and haddocks and enable z3 for select packages
  lhComponent = pkg: nixpkgs.haskell.lib.overrideCabal pkg (
    old: {
      doCheck = false; # TODO
      doHaddock = false; # TODO
      buildTools = old.buildTools or [] ++ [ nixpkgs.z3 ];
    }
  );
in
{ inherit nixpkgs; inherit haskellPackages; }
