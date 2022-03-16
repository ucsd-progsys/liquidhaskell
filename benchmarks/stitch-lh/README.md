StitchLH
========

StitchLH is a reimplementation of [Stitch][stitch] using LiquidHaskell.

Stitch is a full implementation of the simply typed lambda-calculus. The main
`stitch-lh` executable is a REPL, allowing the user to write lambda-expressions and
evaluating them. Run `:help` at the prompt to see other commands.

Under the hood, StitchLH is implemented with a simple abstract syntax tree.
LiquidHaskell is used to ensure that only well-typed Stitch terms can be built
internally. This feat requires little use of modern GHC/Haskell features.

To build and test
```
nix-shell --pure --run "stack --nix test"
```

To run the interpreter
```
nix-shell --pure --run "stack --nix exec stitch-lh"
```

[stitch]: https://gitlab.com/goldfirere/stitch
