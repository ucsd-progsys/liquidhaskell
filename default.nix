/*
 * to build all of the packages in the project
 *
 *    nix-build
 *
 * to get an environment for development of one package in the project
 *
 *    nix-shell --argstr envFor liquidhaskell
 *
 * to extend and override in a new nix expression
 *
 *    Eg. for liquid-fixpoint, which lives in its own repo and shouldn't need to repeat everything
 *    TODO: import this repo's pins.nix and override the haskellPackages it contains
 */
{ envFor ? null, config ? { allowBroken = true; }, ... }:
let
  pins = import ./pins.nix { inherit config; };
in
if envFor == null
then pins.nixpkgs.buildEnv {
  name = "liquidhaskell-project";
  paths = pins.projectPackages;
}
else pins.haskellPackages."${envFor}".env.overrideAttrs (
  old: {
    nativeBuildInputs = old.nativeBuildInputs ++ [
      pins.nixpkgs.cabal-install
      pins.nixpkgs.ghcid
    ];
  }
)
