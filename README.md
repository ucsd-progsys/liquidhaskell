Liquid Fixpoint [![Hackage](https://img.shields.io/hackage/v/liquid-fixpoint.svg)](https://hackage.haskell.org/package/liquid-fixpoint) [![Hackage-Deps](https://img.shields.io/hackage-deps/v/liquid-fixpoint.svg)](http://packdeps.haskellers.com/feed?needle=liquid-fixpoint) [![CircleCI](https://circleci.com/gh/ucsd-progsys/liquid-fixpoint.svg?style=svg)](https://circleci.com/gh/ucsd-progsys/liquid-fixpoint)
===============



This package implements a Horn-Clause/Logical Implication constraint solver used
for various Liquid Types. The solver uses SMTLIB2 to implement an algorithm similar to:

+ [Houdini](https://users.soe.ucsc.edu/~cormac/papers/fme01.pdf)
+ [Cartesian predicate abstraction](http://swt.informatik.uni-freiburg.de/berit/papers/boolean-and-cartesian-....pdf)


Requirements
------------

In addition to the .cabal dependencies you require an SMTLIB2 compatible solver binary:

- [Z3](http://z3.codeplex.com)
- [CVC4](http://cvc4.cs.nyu.edu)
- [MathSat](http://mathsat.fbk.eu/download.html)

If on Windows, please make sure to place the binary and any associated DLLs somewhere
in your path.

How To Build and Install
------------------------

Simply do:

    git clone https://github.com/ucsd-progsys/liquid-fixpoint.git
    cd liquid-fixpoint
    stack install

or (`cabal` instead of `stack` if you prefer.)


Using SMTLIB-based SMT Solvers
------------------------------

You can use one of several SMTLIB2 compliant solvers, by:

    fixpoint --smtsolver=z3 path/to/file.hs

Currently, we support

    * Z3
    * CVC4
    * MathSat



Configuration Management
------------------------

It is very important that the version of Liquid Fixpoint be maintained properly.

Suppose that the current version of Liquid Haskell is `A.B.C.D`:

+ After a release to hackage is made, if any of the components `B`, `C`, or `D` are missing, they shall be added and set to `0`. Then the `D` component of Liquid Fixpoint shall be incremented by `1`. The version of Liquid Fixpoint is now `A.B.C.(D + 1)`

+ The first time a new function or type is exported from Liquid Fixpoint, if any of the components `B`, or `C` are missing, they shall be added and set to `0`. Then the `C` component shall be incremented by `1`, and the `D` component shall stripped. The version of Liquid Fixpoint is now `A.B.(C + 1)`

+ The first time the signature of an exported function or type is changed, or an exported function or type is removed (this includes functions or types that Liquid Fixpoint re-exports from its own dependencies), if the `B` component is missing, it shall be added and set to `0`. Then the `B` component shall be incremented by `1`, and the `C` and `D` components shall be stripped. The version of Liquid Fixpoint is now `A.(B + 1)`

+ The `A` component shall be updated at the sole discretion of the project owners.

It is recommended to use the [Bumper](https://hackage.haskell.org/package/bumper) utility to manage the versioning of Liquid Fixpoint. Bumper will automatically do the correct update to the cabal file. Additionally, it will update any packages that you have the source for that depend on Liquid Fixpoint.

To update Liquid Fixpoint and Liquid Haskell, first clone Liquid Haskell and Liquid Fixpoint to a common location:

```
git clone https://github.com/ucsd-progsys/liquidhaskell.git
git clone https://github.com/ucsd-progsys/liquid-fixpoint.git
```

To increment the `D` component of Liquid Fixpoint:

```
./path/to/bumper -3 liquid-fixpoint
```

This will update the `D` component of Liquid Fixpoint. If necessary, this will update the `Build-Depends` of Liquid Haskell. If the `Build-Depends` was updated, Liquid Haskell's `D` component will be incremented.

To increment the `C` component of Liquid Fixpoint, and strip the `D` component:

```
./path/to/bumper --minor liquid-fixpoint
```

As before, this will update Liquid Fixpoint and, if necessary, Liquid Haskell.

To increment the `B` component of Liquid Fixpoint, and strip the `D` and `C` components:

```
./path/to/bumper --major liquid-fixpoint
```

As before, this will update Liquid Fixpoint and, if necessary, Liquid Haskell

SMTLIB2 Interface
-----------------

There is a new SMTLIB2 interface directly from Haskell:

+ Language.Fixpoint.SmtLib2

See `tests/smt2/{Smt.hs, foo.smt2}` for an example of how to use it.

Options
-------

`--higherorder` allows higher order binders into the environment

`--extsolver` runs the **deprecated** external solver.

`--parts` Partitions an `FInfo` into a `[FInfo]` and emits a bunch of files. So:

    $ fixpoint -n -p path/to/foo.fq

will now emit files:

    path/to/.liquid/foo.1.fq
    path/to/.liquid/foo.2.fq
    . . .
    path/to/.liquid/foo.k.fq

and also a dot file with the constraint dependency graph:

    path/to/.liquid/foo.fq.dot


## FInfo Invariants

### Binders

This is the field

```
     , bs       :: !BindEnv         -- ^ Bind  |-> (Symbol, SortedReft)
```

or in the .fq files as

```
bind 1 x : ...
bind 2 y : ...
```

* Each `BindId` must be a distinct `Int`,
* Each `BindId` that appears in a constraint
  environment i.e. inside _any_ `IBindEnv`
  must appear inside the `bs`

### Environments

* Each constraint's environment is a set of `BindId`
  which must be defined in the `bindInfo`. Furthermore

* Each constraint should not have _duplicate_ names in its
  environment, that is if you have two binders

```
  bind 1 x : ...
  bind 12 x : ...
```

  Then a single `IBindEnv` should only mention _at most_
  one of `1` or `12`.

* There is also a "tree-shape" property that its a bit hard
  to describe ... TODO     

### LHS

Each `slhs` of a constraint is a `SortedReft`.

- Each `SortredReft` is basically a `Reft` -- a logical predicate.
  The important bit is that a `KVar` i.e. terms of the formalized

```
     $k1[x1:=y1][x2:=y2]...[xn:=yn]
```

  That is represented in the `Expr` type as

```
  | PKVar  !KVar !Subst
```

  must appear _only_ at the **top-level** that is not under _any_
  other operators, i.e. not as a sub-`Expr` of other expressions.


- This is basically a predicate that needs to be "well sorted"
  with respect to the `BindId`, intuitively

```
    x:int, y:int |- x + y : int
```

  is well sorted. but

```
    x:int  |- x + y : int
```

  is not, and

```
    x:int, y: list |- x + y : int
```

  is not. The exact definition is formalized in `Language.Fixpoint.SortCheck`


### RHS

Similarly each `rhs` of a `SubC` must either be a single `$k[...]` or an plain `$k`-free `Expr`.

### Global vs. Distinct Literals

```
     , gLits    :: !(SEnv Sort)               -- ^ Global Constant symbols
     , dLits    :: !(SEnv Sort)       
```

The _global_ literals `gLits` are symbols that
are in scope _everywhere_ i.e. need not be separately
defined in individual environments. These include things like

- uninterpreted _measure_ functions `len`, `height`,
- uninterpreted _data constructor_ literals `True`, `False`

Suppose you have an enumerated type like:

```
data Day = Sun | Mon | Tue | Wed | ... | Sat
```

You can model the above values in fixpoint as:

```
constant lit#Sun : Day
constant lit#Mon : Day
constant lit#Tue : Day
constant lit#Wed : Day
```

The _distinct_ literals are a subset of the above where we
want to tell the SMT solver that the values are *distinct*
i.e. **not equal** to each other, for example, you can
**additionally** specify this as:

```
distinct lit#Sun : Day
distinct lit#Mon : Day
distinct lit#Tue : Day
distinct lit#Wed : Day
```

The above two are represented programmatically by generating   
suitable `Symbol` values (for the literals  see `litSymbol`)
and `Sort` values as `FTC FTycon` and then making an `SEnv`
from the `[(Symbol, Sort)]`.

### Sorts

> What's the difference between an FTC and an FObj?

In early versions of fixpoint, there was support for 
three sorts for expressions (`Expr`) that were sent 
to the SMT solver:

1. `int`
2. `bool`
3. "other"

The `FObj` sort was introduced to represent essentially _all_ 
non-int and non-bool values (e.g. tuples, lists, trees, pointers...)

However, we later realized that it is valuable to keep _more_
precise information for `Expr`s and so we introduced the `FTC`
(fixpoint type constructor), which lets us represent the above
respectively as:

- `FTC "String" []`                   -- in Haskell `String`
- `FTC "Tuple"  [FInt, Bool]`         -- in Haskell `(Int, Bool)`
- `FTC "List" [FTC "List" [FInt]]`    -- in Haskell `[[Int]]`

> There is a comment that says FObj's are uninterpretted types;
> so probably a type the SMT solver doesn't know about?
> Does that then make FTC types that the SMT solver does
> know about (bools, ints, lists, sets, etc.)?

The SMT solver knows about `bool`, `int` and `set` (also `bitvector` 
and `map`) but _all_ other types are _currently_ represented as plain 
`Int` inside the SMT solver. However, we _will be_ changing this 
to make use of SMT support for ADTs ...

To sum up: the `FObj` is there for historical reasons; it has been 
subsumed by `FTC` which is what I recomend you use. However `FObj` 
is there if you want a simple "unitype" / "any" type for terms 
that are not "interpreted".

