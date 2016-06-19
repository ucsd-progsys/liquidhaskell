{ nixpkgs ? import <nixpkgs> {}, compiler ? "default", profiling ? false }:

let

  inherit (nixpkgs) pkgs;

  liquid-fixpoint = import ./liquid-fixpoint { inherit (pkgs) fetchgitLocal; };

  f = import ./default.nix { inherit (pkgs) fetchgitLocal; };

  haskellPackages = (if compiler == "default"
                     then pkgs.haskellPackages
                     else pkgs.haskell.packages.${compiler}
                    ).override {
                      overrides = self: super: {
                        liquid-fixpoint = (self.callPackage liquid-fixpoint { inherit (pkgs) z3; }).overrideDerivation (drv: { doCheck = false; });

                        mkDerivation = drv: super.mkDerivation (drv // { enableLibraryProfiling = profiling; });
                      };
                    };

  drv = haskellPackages.callPackage f { inherit (pkgs) z3; };

in

  if pkgs.lib.inNixShell then drv.env else drv
