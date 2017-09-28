# Running LiquidHaskell with Nix

Via [Gabriel Gonzalez](https://github.com/Gabriel439), 
see [this issue](https://github.com/ucsd-progsys/liquidhaskell/issues/1099) for details.

Nix lets you create transient GHC environments with corresponding 
package databases that may be needed to run LH on specific programs.

1. Create shell, that lists the extra dependencies: 

- the version of GHC (must be the same as you build LH with, e.g. GHC 8.0.2)
- any extra libraries (e.g. `vector`) 


```
$ nix-shell --packages 'haskell.packages.ghc802.ghcWithPackages (pkgs: [ pkgs.vector ])'
```

2. Set environment variables

```
[nix-shell]$ eval "$(egrep ^export "$(type -p ghc)")"
```

3. Run LH

```
[nix-shell]$ liquid examples/search.hs
```

Steps 1-3 can be encapsulated in a single `shell.nix` e.g. 

```nix
let
  inherit (import <nixpkgs> { }) fetchFromGitHub;

  nixpkgs = fetchFromGitHub {
    owner = "NixOS";

    repo = "nixpkgs";

    rev = "1715436b75696d9885b345dd8159e12244d0f7f5";
    sha256 = "18qp76cppm1yxmzdaak9kcllbypvv22c9g7iaycq2wz0qkka6rx5";
  };

  pkgs = import nixpkgs { };

  liquid =
    pkgs.runCommand "liquidhaskell" { buildInputs = [ pkgs.makeWrapper ]; } ''
      mkdir -p $out/bin
      ln -s ${pkgs.haskellPackages.liquidhaskell}/bin/liquid $out/bin
      wrapProgram $out/bin/liquid --prefix PATH : ${pkgs.z3}/bin
    '';

  ghc = pkgs.haskellPackages.ghcWithPackages (ps: with ps; [
          vector
        ]);
in
  pkgs.stdenv.mkDerivation {
    name = "my-haskell-env-0";
    buildInputs = [ ghc liquid ];
    shellHook = "eval $(egrep ^export ${ghc}/bin/ghc)";
  }
```



