# Report: Type-Literal Tests for Liquid Haskell

This document summarises the tests created in `tests/typelits/` that cover
support for GHC type literals (`Nat` and `Symbol` kinds) in LH.  The tests are
grouped into positive (LH should accept) and negative (LH should reject).

The features under test are tracked by
[issue #2447](https://github.com/ucsd-progsys/liquidhaskell/issues/2447),
[issue #2702](https://github.com/ucsd-progsys/liquidhaskell/issues/2702), and
commits
[e66bef1](https://github.com/ucsd-progsys/liquidhaskell/commit/e66bef1eec9c0d3ca2e74684410f38814d045c03),
[43496cf](https://github.com/ucsd-progsys/liquidhaskell/commit/43496cf3cee473e2a8de3db8f1e7abffd17aa4b3), and
[77c0776](https://github.com/ucsd-progsys/liquidhaskell/commit/77c0776ea00c45b6522d736af88364e515c0bdf9).

Run the tests with:

```
scripts/test/test_plugin.sh typelits-pos typelits-neg
```

---

## Positive tests (`tests/typelits/pos/`)

### `NatLit.hs` — Nat literal substitution (issue #2447)

**Property tested:** When a data type is parameterised by a concrete `Nat`
literal, `caseEnv` (via `tyLitSubst`) must substitute the literal value for
the type-parameter name in the constructor's refinements at the pattern-match
site.

- `EmptyIfZero n` has constructor precondition `{v:Int | n /= 0}`.  At `n=0`
  this becomes `{v:Int | 0 /= 0} = {v:Int | false}`, so `EmptyIfZero 0` is
  uninhabited and a pattern match on it is safe (no viable scrutinee exists).
- `EmptyIfZero 1` and `EmptyIfZero 3` can be constructed.
- `Exact n` stores `{v:Int | v == n}`.  Matching on `Exact 3` reveals `v == 3`.
- Polymorphic `getExact :: Exact n -> {v:Int | v == n}` works for a free Nat
  type variable.

**Key pipeline fix required:**  `caseEnv` in `Constraint/Generate.hs` —
add `tyLitSubst` to substitute concrete literal values after `unfoldR`.

---

### `NatArith.hs` — Nat arithmetic in type positions (commit e66bef1, 43496cf)

**Property tested:** `argType` is extended to translate type-level arithmetic
(`+`, `-`, `*`, `Div`, `Mod`) into Fixpoint `EBin` expressions.  The
`checkAppTys` check accepts `RExprArg` without error, and `exprArgCompat`
allows structural comparison between `RExprArg (n+1)` (LH) and
`RApp (+) [n, 1]` (GHC).

- `SumSucc (n+1)` — the type argument is an arithmetic expression; after
  substitution the field satisfies `v == n+2`.
- Concrete construction: `SumSucc 0` (field=1), `SumSucc 4` (field=5).
- `SubOne`, `Doubled`, `Halved`, `Modded` — analogous tests for `-`, `*`,
  `Div`, `Mod` with both concrete literals and (for `Doubled`) a polymorphic
  argument `Doubled (n*2) -> {v:Int | v == n*4}`.

**Key pipeline fixes required:**
- `argType`: handle `TyConApp tc [a, b]` via `natTyConBop`.
- `checkAppTys`: `go (RExprArg _) = Nothing`.
- `tyCompat`: `exprArgCompat` fallback for `RExprArg` vs `RApp`.
- `caseEnv`/`tyLitSubst`: substitute arithmetic expressions too.

---

### `NatVec.hs` — Nat-indexed GADT vector (issue #2702)

**Property tested:** A GADT `Vec n a` uses Nat literals (`0`) and arithmetic
(`n+1`) in constructor return types.  The measure `vlen` counts elements.
Safe indexing `at :: v:Vec n a -> {i:Int | 0 <= i && i < vlen v} -> a` is
verified total:

- Matching on `VNil` reveals `n = 0` (GADT constraint), hence `vlen v = 0`.
  The precondition `0 <= _ && _ < 0` is unsatisfiable, making the `VNil`
  branch unreachable.
- Concrete access to a three-element vector at indices 0 and 2 is accepted.
- `hd` and `tl` require `vlen v >= 1`; their `VNil` branches are unreachable.

**Key pipeline fixes required:** All of the above, plus correct handling of
GADT equality constraints so that `n ~ 0` is propagated into the environment.

Note: the LIQUID data annotation with GADT-style constructor return types
(`VCons :: a -> Vec n a -> Vec (n+1) a`) currently fails to parse because
`n` in `(n+1)` is unresolved in the LH data annotation context.  This
annotation is commented out in the test; it should be restored when LH
supports Nat arithmetic in LIQUID data annotations.

---

### `NatTypeSyn.hs` — Nat type synonyms and type families

**Property tested:** GHC type synonyms (`Zero`, `Two`, `Succ n`) and closed
type families (`Plus2 n`) that expand to Nat literals or arithmetic can be
used in LH specs.  GHC expands transparent synonyms before LH sees them,
so LH ultimately processes the underlying literal or arithmetic expression.

- `Exact Zero` (= `Exact 0`), `Exact Two` (= `Exact 2`).
- `Exact (Succ 4)` (= `Exact (4+1)` = `Exact 5`).
- `Exact (Plus2 3)` (= `Exact 5`, reduced by GHC before LH).
- Pattern-matching on `Exact Zero` reveals the field equals 0.

**Key pipeline fixes required:** Same as `NatLit.hs` and `NatArith.hs`.

---

### `NatAlias.hs` — LH type and predicate aliases with Nat arguments

**Property tested:** LH type aliases and predicate aliases can take Nat
expressions as arguments, in two distinct roles:

1. **Value role** (`GtN N` — N appears in a refinement `v > N`): a Nat
   literal like `5` becomes the logical integer `ECon (I 5)`; a Nat type
   variable `n` becomes `EVar n`.
2. **Predicate alias** (`GtNP N V = V > N`): same treatment for predicate
   aliases.

- `GtN 5` — the integer-greater-than-5 type; `moreThan5 = 6` is accepted.
- `moreThanN :: forall (n :: Nat). Exact n -> GtN n` — uses the Nat type
  variable `n` as the value argument to `GtN`; the output refinement
  `{v:Int | v > n}` references the Nat type parameter.
- `BetweenNM 3 7` — two Nat literal value arguments; tested with concrete
  values.
- `predicate GtNP N V = V > N` — predicate alias analogue.

Note: using a Nat type variable in the *input* refinement position
(e.g. `{v:Int | v > n} -> ...`) requires Nat type vars to be fully lifted
into the logic environment for function specs, which is part of the feature
under test.  Functions using Nat type vars only in *output* refinements or
via aliases already work with the current implementation.

**Key pipeline fixes required:** The output-refinement cases (`moreThanN`,
`moreThan10`) already pass.  The input-refinement cases depend on the same
fixes as `NatLit.hs`.

---

### `SymbolLit.hs` — Symbol type literals (commit 77c0776)

**Property tested:** `Symbol` type literals (string literals at the kind
level) are handled correctly.  LH encodes `Symbol` type variables as sort
`[Char]` in Fixpoint (via `ofLitType`), and `ESym "foo"` is recognised as
having `SymbolKind`.

- `Labeled "foo" Int` and `Labeled "bar" Bool` — construction with Symbol
  literals.
- `Bucket s` with `{bName :: {v:String | v == s}}` — the Symbol parameter is
  used in a string-equality refinement.
- `mkHelloBucket :: Bucket "hello"` — `bName` must equal `"hello"`.
- `getName :: Bucket s -> {v:String | v == s}` — polymorphic Symbol getter.

**Key pipeline fixes required:**
- `exprArgKind` to classify `ESym` as `SymbolKind`.
- `exprArgKindType` to map `SymbolKind` → `stringTy` (not `typeSymbolKind`).
- `rSortIsSymbolKind` to recognise the `[Char]` structure that LH uses for
  Symbol.

---

### `SymbolConstraints.hs` — Symbol type variables in refinements

**Property tested:** A `NamedBucket s` records a `String` field that must
equal the Symbol parameter `s`.  Matching reveals the string value.

- `mkAlice :: NamedBucket "alice"` — construction at a concrete Symbol.
- `getAliceName :: NamedBucket "alice" -> {v:String | v == "alice"}`.
- `getBucketName :: NamedBucket s -> {v:String | v == s}` — polymorphic.
- LH type alias `BucketOf S` and predicate alias `HasName S V = V == S`
  with Symbol arguments.

**Key pipeline fixes required:** Same as `SymbolLit.hs`.

---

## Negative tests (`tests/typelits/neg/`)

### `NatArithUnsafe.hs` — incorrect arithmetic claim

**Property tested:** A wrong postcondition is rejected.

`Counter (n+1)` holds `{v:Int | v == n+1}`.  The spec for `getCounter` claims
`{v:Int | v == n+2}`.  Since `n+1 ≠ n+2`, LH should report an unsafe
constraint.

**Expected error:** `Liquid Type Mismatch` / unsafe constraint.

---

### `NatSymbolMismatch.hs` — kind mismatch: Nat at Symbol position

**Property tested:** Using a `Nat` literal where a `Symbol` is expected is
rejected by LH with a kind-mismatch error.

`Labeled` is parameterised by `s :: Symbol`.  The LH spec `{-@ mkBad ::
Labeled 42 Int @-}` uses the Nat literal `42` in the Symbol position.  LH
should detect the mismatch (Nat vs Symbol kind) and report an error.

**Expected error:** Kind-mismatch / type-refinement error from LH's spec
checker.

---

## Coverage gaps and future tests

The current tests focus on the core pipeline.  The following cases could be
added once the basic support is in place:

- Nat exponentiation (`^`) — not currently supported because Fixpoint has no
  `EBin Exp` counterpart.
- `KnownNat` and `natVal` — runtime reification of type literals.
- Interaction with `PLE` (proof-by-logical-evaluation) for Nat-arithmetic
  lemmas.
- Multi-parameter type families that compute Nat results (e.g.
  `GCD`, `LCM`).
- `CmpNat` / `OrdCond` — comparison type families.
