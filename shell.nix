{ nixpkgs ? import <nixpkgs> {}, compiler ? "default", doBenchmark ? false }:

let

  inherit (nixpkgs) pkgs;

  f = { mkDerivation, aeson, array, base, bifunctors, binary
      , bytestring, Cabal, cereal, cmdargs, containers, data-default
      , deepseq, Diff, directory, exceptions, filepath, fingertree, ghc
      , ghc-boot, ghc-paths, ghc-prim, gitrev, hashable, hpc, hscolour
      , liquid-fixpoint, located-base, mtl, optparse-applicative
      , optparse-simple, parsec, pretty, process, QuickCheck, stdenv, stm
      , syb, tagged, tasty, tasty-ant-xml, tasty-hunit, tasty-rerun
      , template-haskell, temporary, text, text-format, th-lift, time
      , transformers, unordered-containers, vector, z3
      }:
      mkDerivation {
        pname = "liquidhaskell";
        version = "0.8.4.0";
        src = ./.;
        isLibrary = true;
        isExecutable = true;
        enableSeparateDataOutput = true;
        libraryHaskellDepends = [
          aeson array base bifunctors binary bytestring Cabal cereal cmdargs
          containers data-default deepseq Diff directory exceptions filepath
          fingertree ghc ghc-boot ghc-paths ghc-prim gitrev hashable hpc
          hscolour liquid-fixpoint located-base mtl optparse-simple parsec
          pretty process QuickCheck syb template-haskell temporary text
          text-format th-lift time transformers unordered-containers vector
        ];
        executableHaskellDepends = [
          base cmdargs deepseq ghc ghc-boot hpc liquid-fixpoint located-base
          pretty process time
        ];
        testHaskellDepends = [
          array base bytestring containers directory filepath ghc ghc-boot
          hpc liquid-fixpoint mtl optparse-applicative parsec process stm syb
          tagged tasty tasty-ant-xml tasty-hunit tasty-rerun template-haskell
          text time transformers
        ];
        testSystemDepends = [ z3 ];
        homepage = "https://github.com/ucsd-progsys/liquidhaskell";
        description = "Liquid Types for Haskell";
        license = stdenv.lib.licenses.bsd3;
      };

  haskellPackages = if compiler == "default"
                       then pkgs.haskellPackages
                       else pkgs.haskell.packages.${compiler};

  variant = if doBenchmark then pkgs.haskell.lib.doBenchmark else pkgs.lib.id;

  drv = variant (haskellPackages.callPackage f {});

in

  if pkgs.lib.inNixShell then drv.env else drv
