{pkgs ? import ./nixpkgs.nix {}}:

with pkgs;

mkShell {
  LANG="C.UTF-8";

  buildInputs = [
    cacert
    git
    glibcLocales
    gnuplot
    hostname
    less
    nix
    stack
    which
    z3
  ];

}
