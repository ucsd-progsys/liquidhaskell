{ makeEnv ? false, config ? { allowBroken = true; }, ... }:
let
  pins = import ./pins.nix { inherit config; };
in
pins.nixpkgs.buildEnv {
  name = "liquidhaskell-packages";
  paths = with pins.haskellPackages; [
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
}
