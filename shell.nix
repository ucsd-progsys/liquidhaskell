{ nixpkgs ? import <nixpkgs> {}, compiler ? "default" }:

let

  inherit (nixpkgs) pkgs;

  f = import ./default.nix { inherit (pkgs) fetchgitLocal; };

  haskellPackages = if compiler == "default"
                       then pkgs.haskellPackages
                       else pkgs.haskell.packages.${compiler};

  drv = haskellPackages.callPackage f { inherit (pkgs) z3; };

in

  if pkgs.lib.inNixShell then drv.env else drv
