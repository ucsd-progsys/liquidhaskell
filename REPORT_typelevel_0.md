# Report: Type-Level Natural Literals in GADT Reflection

## Problem

Running `cabal exec -- ghc -fplugin=LiquidHaskell Test1.hs -fforce-recomp` failed with:

```
Illegal type specification for `Test1.vmap`
Sort Error in Refinement: ...
Unbound symbol 0 --- perhaps you meant: n ?
  because
Cannot unify fix$36$0 with int in expression: Test1.$WNil
  because
Cannot cast Test1.$WNil of sort (Test1.Vec int @(1001))
  to incompatible sort (Test1.Vec fix$36$0 b##aNx)
```

The reflected `vmap` function over a GADT `Vec` (indexed by type-level `Nat`)
generated sort-incorrect coercion terms.

## Root Cause

When reflecting a function that pattern-matches on a GADT with type-level
natural indices (e.g., `Vec (0 :: Nat) a`), LiquidHaskell generates `ECoerc`
(coercion) terms whose source/target sorts are computed by `typeSort` in
`RefType.hs`.

The `typeSort` function had **no case for `LitTy (NumTyLit _)`** (type-level
numeric literals like `0 :: Nat` or `1 :: Nat`). These fell through to the
catch-all:

```haskell
go τ = FObj (typeUniqueSymbol τ)
```

This produced `FObj "0"` — an uninterpreted sort symbol. Due to
liquid-fixpoint's symbol encoding (`prefixAlpha` adds `fix$` for
non-alpha-starting symbols, and `$` is encoded as `$36$`), this rendered as
`fix$36$0`.

Meanwhile, the data constructor `Nil :: Vec Zero a` had its sort computed
through a *different* path (`ofLitType` in `ofType`), which correctly maps
`NumTyLit _` to `intTyCon`, yielding sort `FInt`.

The sort-checker tried to unify `FInt` with `FObj "fix$0"`, failed to find
`"fix$0"` in the sort environment, and reported "Unbound symbol 0".

Similarly, type family applications like `n + 1` (from `Succ n = n + 1`) of
kind `Nat` were processed as sort-level applications of uninterpreted type
constructors, producing complex sorts like
`FApp (FTC "GHC.Internal.TypeNats.+") [FObj "n", FObj "1"]` instead of `FInt`.

## Fix

Added two cases to `typeSort` in
`liquidhaskell-boot/src/Language/Haskell/Liquid/Types/RefType.hs`:

1. **`LitTy (NumTyLit _)` → `FInt`**: Type-level numeric literals always have
   kind `Nat`, which is embedded as `Int` in the refinement logic.

2. **Type family TyCons with `Nat` result kind → `FInt`**: When a type family
   (like `GHC.TypeNats.+`) is fully applied and its result kind is `naturalTy`,
   the sort is `FInt`. This handles expressions like `n + 1` in GADT
   constructor return types.

```haskell
go (TyConApp c τs)
  | ...
  | Ghc.isFamilyTyCon c
  , Ghc.piResultTys (Ghc.tyConKind c) τs `Ghc.eqType` naturalTy
  = FInt
  | otherwise
  = tyConFTyCon tce c (go <$> τs)
...
go (LitTy (NumTyLit _)) = FInt
```

## Verification

- `Test1.hs` now reports: `LIQUID: SAFE (4 constraints checked)`
- All existing tests pass (`scripts/test/test_plugin.sh`, `cabal test liquid-fixpoint`)
