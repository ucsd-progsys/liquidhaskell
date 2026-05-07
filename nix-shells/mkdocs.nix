{ pkgs ? import <nixpkgs> {} }:

let
  python = pkgs.python314;
  pythonPackages = pkgs.python314Packages;
  mkdocs = pythonPackages.mkdocs;
  mkdocsMaterial = pythonPackages.mkdocs-material;
  awesomePages = pythonPackages.mkdocs-awesome-nav;
in pkgs.mkShell {
  buildInputs = [
    pkgs.git
    mkdocs
    mkdocsMaterial
    awesomePages
  ];

  shellHook = ''
    echo "Shell with mkdocs and plugins available (mkdocs --version: $(mkdocs --version 2>/dev/null || true))"
  '';
}

