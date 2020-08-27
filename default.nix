{ makeEnv ? false, config ? { /*allowBroken = true;*/ }, ... }:
let
  nixpkgs = import (
    builtins.fetchTarball {
      # fetch latest nixpkgs https://github.com/NixOS/nixpkgs-channels/tree/nixos-20.03 as of Tue 18 Aug 2020 02:51:27 PM UTC
      url = "https://github.com/NixOS/nixpkgs-channels/archive/cb1996818edf506c0d1665ab147c253c558a7426.tar.gz";
      sha256 = "0lb6idvg2aj61nblr41x0ixwbphih2iz8xxc05m69hgsn261hk3j";
    }
  ) { inherit config; };
  # function to make sure a haskell package has z3 at build-time and test-time
  usingZ3 = pkg: nixpkgs.haskell.lib.overrideCabal pkg (old: { buildTools = old.buildTools or [] ++ [ nixpkgs.z3 ]; });
  # override haskell compiler version, add and override dependencies in nixpkgs
  haskellPackages = nixpkgs.haskell.packages."ghc8101".override (
    old: {
      all-cabal-hashes = nixpkgs.fetchurl {
        # fetch latest cabal hashes https://github.com/commercialhaskell/all-cabal-hashes/tree/hackage as of Tue 18 Aug 2020 02:51:27 PM UTC
        url = "https://github.com/commercialhaskell/all-cabal-hashes/archive/112fef7b4bf392d4d4c36fbbe00ed061685ba26c.tar.gz";
        sha256 = "0x0mkpwnndw7n62l089gimd76n9gy749giban9pacf5kxbsfxrdc";
      };
      overrides = self: super: with nixpkgs.haskell.lib; rec {
        mkDerivation = args: super.mkDerivation (
          args // {
            doCheck = false;
            doHaddock = false;
            jailbreak = true;
          }
        );
        liquid-base = usingZ3 (self.callCabal2nix "liquid-base" ./liquid-base {});
        liquid-bytestring = (self.callCabal2nix "liquid-bytestring" ./liquid-bytestring {});
        liquid-containers = (self.callCabal2nix "liquid-containers" ./liquid-containers {});
        liquid-fixpoint = (self.callCabal2nix "liquid-fixpoint" ./liquid-fixpoint {});
        liquid-ghc-prim = usingZ3 (self.callCabal2nix "liquid-ghc-prim" ./liquid-ghc-prim {});
        liquid-parallel = (self.callCabal2nix "liquid-parallel" ./liquid-parallel {});
        liquid-platform = (self.callCabal2nix "liquid-platform" ./liquid-platform {});
        liquid-prelude = (self.callCabal2nix "liquid-prelude" ./liquid-prelude {});
        liquid-vector = (self.callCabal2nix "liquid-vector" ./liquid-vector {});
        liquidhaskell = (self.callCabal2nix "liquidhaskell" ./. {});
        # TODO turn on tests only for these LH packages
        #   separate tests

        # # using latest hackage releases as of Tue 18 Aug 2020 02:51:27 PM UTC
        hashable = self.callHackage "hashable" "1.3.0.0" {}; # ouch; requires recompilation of around 30 packages
        # memory = self.callHackage "memory" "0.15.0" {};
        optics = self.callHackage "optics" "0.3" {};
        optics-core = self.callHackage "optics-core" "0.3.0.1" {};
        optics-extra = self.callHackage "optics-extra" "0.3" {};
        optics-th = self.callHackage "optics-th" "0.3.0.1" {};
        # tls = self.callHackage "tls" "1.5.4" {};
      };
    }
  );
  # function to bring devtools in to a package environment
  devtools = old: { nativeBuildInputs = old.nativeBuildInputs ++ [ nixpkgs.cabal-install nixpkgs.ghcid ]; }; # ghc and hpack are automatically included
  # ignore files specified by gitignore in nix-build
  source = nixpkgs.nix-gitignore.gitignoreSource [] ./.;
  # use overridden-haskellPackages to call gitignored-source
  drv = nixpkgs.haskell.lib.overrideCabal haskellPackages.liquidhaskell (
    old: {
      passthru = old.passthru // {
        nixpkgs = nixpkgs;
        haskellPackages = haskellPackages;
      };
    }
  );
in
if makeEnv then drv.env.overrideAttrs devtools else drv
# use buildenv or shellenv to build all of them here
# use relative
