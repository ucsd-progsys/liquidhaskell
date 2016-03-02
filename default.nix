{ fetchgitLocal }:
{ mkDerivation, aeson, array, base, bifunctors, bytestring, Cabal
, cereal, cmdargs, containers, cpphs, daemons, data-default
, deepseq, Diff, directory, filepath, fingertree, ghc, ghc-paths
, hashable, hpc, hscolour, liquid-fixpoint, located-base, mtl
, network, optparse-applicative, parsec, pretty, process, prover
, stdenv, stm, syb, tagged, tasty, tasty-hunit, tasty-rerun
, template-haskell, text, time, transformers, unix
, unordered-containers, vector, z3
, tasty-ant-xml
}:
mkDerivation {
  pname = "liquidhaskell";
  version = "9.9.9.9";
  src = fetchgitLocal ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    aeson array base bifunctors bytestring Cabal cereal cmdargs
    containers cpphs data-default deepseq Diff directory filepath
    fingertree ghc ghc-paths hashable hpc hscolour liquid-fixpoint
    located-base mtl parsec pretty process prover syb template-haskell
    text time unordered-containers vector hscolour
  ];
  executableHaskellDepends = [
    base bytestring cereal cmdargs daemons data-default deepseq
    directory ghc liquid-fixpoint located-base network pretty process
    prover unix unordered-containers
  ];
  testHaskellDepends = [
    base containers directory filepath mtl optparse-applicative process
    stm tagged tasty tasty-hunit tasty-rerun transformers tasty-ant-xml
  ];
  testSystemDepends = [ z3 ];
  homepage = "http://goto.ucsd.edu/liquidhaskell";
  description = "Liquid Types for Haskell";
  license = stdenv.lib.licenses.bsd3;
}
