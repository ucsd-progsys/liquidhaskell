# Installing LiquidHaskell

To run LiquidHaskell you need to install:

1. An SMT solver

2. LH itself as one of:
    a. A GHC compiler plugin
    b. A standalone binary

We **strongly recommend** the [plugin][lh-plugin-demo], the binary is left for backwards compatibility.

You can install the `liquid` binary via package manager *or* source.

## 1. Install SMT Solver

Download and install *at least one* of

+ [Z3](https://github.com/Z3Prover/z3/releases) or [Microsoft official binary](https://www.microsoft.com/en-us/download/details.aspx?id=52270)
+ [CVC4](http://cvc4.cs.stanford.edu/web/)
+ [MathSat](http://mathsat.fbk.eu/download.html)

**Note:** The SMT solver binary should be on your `PATH`; LiquidHaskell will execute it as a child process.

## 2a. GHC Compiler Plugin

**TODO: Add instructions here**

## 2b. (Legacy) Binary

You can install the `liquid` binary via package manager *or* source.

### Via Package Manager

The `liquid` executable is provided as part of a standalone,
battery-included package called `liquid-platform`.

Simply do:

    cabal install liquid-platform

We are working to put `liquid` on `stackage`.

You can designate a specific version of LiquidHaskell to
ensure that the correct GHC version is in the environment. 
As an example,

    cabal install liquid-platform-0.9.0.0

### Build from Source

If you want the most recent version, you can build from source as follows,
either using `stack` (recommended) or `cabal`. In either case:

1. *recursively* `clone` the repo 

    git clone --recursive https://github.com/ucsd-progsys/liquidhaskell.git
    cd liquidhaskell

2. `build` the package with [stack][stack] 

    stack install liquid-platform

3. or with [cabal][cabal] 

    cabal v2-build liquid-platform

### A note on the GHC_PACKAGE_PATH

To work correctly `liquid` requires access to auxiliary packages
installed as part of the executable. Therefore, you might need to 
extend your `$GHC_PACKAGE_PATH` to have it point to the right location(s). 

Typically the easiest way is to call `stack path`, which will print 
a lot of diagnostic output. From that it should be suffient to copy 
the paths printed as part of `ghc-package-path: <some-paths>` and 
extend the `GHC_PACKAGE_PATH` this way (typically editing your `.bashrc` 
to make the changes permanent):

```
export GHC_PACKAGE_PATH=$GHC_PACKAGE_PATH:<some-paths>
```

After that, running `liquid` anywhere from the filesystem should work.

## Troubleshooting

1. If you're on Windows, please make sure the SMT solver is installed
    in the **same** directory as LiquidHaskell itself (i.e. wherever
    `cabal` or `stack` puts your binaries). That is, do:

    ```
    which liquid
    ```

    and make sure that `z3` or `cvc4` or `mathsat` are in the `PATH`
    returned by the above.

2. If you installed via `stack` and are experiencing path related woes, try:

    ```
    stack exec -- liquid path/to/file.hs
    ```

## Usage with Nix

**NOTE:** These instructions may be superceded by the _plugin-mode_ which simply uses 
plain package dependencies to manage all modules.

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






[stack]: https://github.com/commercialhaskell/stack/blob/master/doc/install_and_upgrade.md
[cabal]: https://www.haskell.org/cabal/