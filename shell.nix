{pkgs ? import ./nixpkgs.nix {}}:

with pkgs;

mkShell {
  LANG="C.UTF-8";

  buildInputs = [
    less
    git
    hostname
    nix
    stack
    z3
    which
    glibcLocales
    cacert
  ];

}
