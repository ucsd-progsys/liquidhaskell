# Running LiquidHaskell

## Plugin

**As of Q2 2020, LiquidHaskell is now available as a GHC [compiler plugin][], 
but we still offer a temporary executable (which uses the plugin internally) 
to give users enough time to complete migrations to the new system**. 

In plugin mode, you

- Tell GHC to use LH during compilation
- Get refinement type errors during compilation
- Reuse editor tooling across. 

In the rest of the section we will refer to the `liquid` executable 
but virtually all the commands shown below are easily portable to 
the plugin. For a more thorough description of how the source plugin
works, checkout the [Tutorial](src/Language/Haskell/Liquid/GHC/Plugin/Tutorial.hs) 
documentation.

**We recommend switching to the new compiler plugin as soon as possible.**

## Editor Support

**In plugin-mode** you get to automatically reuse all `ghc` based support for your editor as is.

To get Liquid Haskell in your editor use the Haskell IDE Engine 
and activate the liquid plugin. For example, 

### VS Code

1. Install the [haskell-ide-engine](https://github.com/haskell/haskell-ide-engine)
2. Enable Haskell Language Server extension from VS Code. 
3. In the VS Code settings search for `liquid` and enable the `Liquid On` extension.

### Emacs 

Use the [Flycheck mode](https://github.com/ucsd-progsys/liquid-types.el)

### Vim

Use the [Syntastic plugin](https://github.com/ucsd-progsys/liquid-types.vim)

## Running the Binary

To verify a file called `foo.hs` at type

    $ liquid foo.hs

## Running in GHCi

To run inside `ghci` e.g. when developing do:

    $ stack ghci liquidhaskell
    ghci> :m +Language.Haskell.Liquid.Liquid
    ghci> liquid ["tests/pos/Abs.hs"]

See [this file](install.md) for instructions on running inside a custom `nix`-shell.

