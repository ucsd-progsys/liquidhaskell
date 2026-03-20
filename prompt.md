I need to fix a test. You can build with
```
cabal build liquidhaskell
```

To run the test use
```
cabal exec -- ghc -fplugin=LiquidHaskell Test.hs -fforce-recomp
```

The problem is that Liquid Haskell is generating selectors for types
mentioned in the type signature of reflected functions. In this example,
the selectors are not possible to generate for reasons that are not
important now.

Liquid Haskell should use a different strategy. Selectors should be generated
for the types of data constructors that are actually used in the bodies of
reflected functions or functions used to create measures with the `measure` annotation.

The code that selects the types for which to create selectors is in
@liquidhaskell-boot/src/Language/Haskell/Liquid/Bare.hs in function
`makeLiftedSpec0`.

Please, change the implementation so the selected types are those of data constructors actually used.

For now we can only collect types from functions in the current module.
