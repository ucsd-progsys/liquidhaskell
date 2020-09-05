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
