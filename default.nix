{ fetchgitLocal }:
{ mkDerivation, ansi-terminal, array, ascii-progress, async
, attoparsec, base, bifunctors, binary, boxes, bytestring, cereal
, cmdargs, containers, deepseq, directory, filemanip, filepath
, ghc-prim, hashable, intern, located-base, mtl, parallel, parsec, pretty
, process, stdenv, syb, tasty, tasty-hunit, tasty-rerun, text
, text-format, transformers, unordered-containers, z3
, dotgen, fgl, fgl-visualize
}:
mkDerivation {
  pname = "liquid-fixpoint";
  version = "9.9.9.9";
  src = fetchgitLocal ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    ansi-terminal array ascii-progress async attoparsec base bifunctors
    binary boxes bytestring cereal cmdargs containers deepseq directory
    filemanip filepath ghc-prim hashable intern located-base mtl parallel parsec
    pretty process syb text text-format transformers
    unordered-containers
    dotgen fgl fgl-visualize
  ];
  executableHaskellDepends = [ base ];
  testHaskellDepends = [
    base directory filepath process tasty tasty-hunit tasty-rerun text
  ];
  testSystemDepends = [ z3 ];
  homepage = "https://github.com/ucsd-progsys/liquid-fixpoint";
  description = "Predicate Abstraction-based Horn-Clause/Implication Constraint Solver";
  license = stdenv.lib.licenses.bsd3;
}
