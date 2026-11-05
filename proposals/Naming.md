# Name Representation and Resolution
We'd like to continue with the work on name resolution and representation. The
goal would be to remove the need to make the text representation of names (i.e.
Symbol) unique, and further standardize on `LHName` as the representation of
names after resolution.

## Motivation
We are primarily interested in improving the support of mentioning type
variables in refinements, an approach broadly used in the [Clash
Prelude](https://hackage-content.haskell.org/package/clash-prelude-1.8.2/docs/Clash-Sized-Index.html).
An example is the type that represents non-negative integers under a type-given
bound:

```haskell
data Index (n :: Nat) =
    Index Natural

{-@
data Index n =
    Index (value :: {v : Natural | v < n})
@-}

add :: Index n -> Index m -> Index (n + m)
add (Index i) (Index j) = Index (i + j)
```

There already is some support for mentioning value-kinded type variables from
function signatures, but this is under the assumption that their names are made
unique, which they aren't in the case of type variables. This is a problem in
e.g. `Constraint.Split`, which can then wrongly replace type variables.

## Approach
To keep the work review-able we suggest to split the work into chunks:

* Generalize declared names ("bindings") to a type variable `b` - most of which
  are currently just `Symbol`:
  * In `Subable` (the one in `liquid-fixpoint`) (1)
  * In `ExprV` and associated data types in `liquid-fixpoint` (2)
  * In `RTypeV` and associated data types (3)

* Attach a `LHUnique` value to the variants of `LHName` mirroring GHC's approach
  to making names unique:
  * Add such an `LHUnique`, as well as a class `Monad m => LHUniqueM m` that can
    generate fresh values of `LHUnique`. (4)
  * Insist that `makeLocalLHName` and friends make names in an `LHUniqueM m`,
    intially just making an escape hatch that gives a constant `LHUnique` (5)

* Use generic bindings and `LHUnique` to our benefit:
  * Split name resolution into a pass that changes `b` from `Symbol` to
    `LHName`, generating a `LHUnique` for each binding site ... (6)
  * ... and the portion changing `v` from `Symbol` to `LHName`, which should not
    need to generate new `LHName`s, instead taking them from the (local or
    global) environment. (7)

* Keep `LHName` as the standard for name representation:
  * At least up to `Constraint.Split`, which still has to do variable
    substitution. (8)
  * Translate back from `LHName` to `Symbol` towards the end of the chain, using
    its attached `LHUnique` to generate a unique name trivially. (9)
