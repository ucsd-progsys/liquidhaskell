# Changes

## Next

## 0.9.10.1 (2024-08-21)

- Add support for GHC 9.10.1.

## 0.9.8.2 (2024-08-21)

- Support for GHC 9.8.2.
- Implement assume-reflect, a feature to assume the reflection of functions in dependencies [2313](https://github.com/ucsd-progsys/liquidhaskell/pull/2313).
- Fixed the polymorphism-related crash in liquid-fixpoint caused by a restrictive theory encoding [#2272](https://github.com/ucsd-progsys/liquidhaskell/issues/2272).

## 0.9.8.1 (2024-02-05)

- Set support for GHC 9.8.1 [#2248](https://github.com/ucsd-progsys/liquidhaskell/pull/2248)
- Embedded files `include/CoreToLogic.lg` and `syntax/liquid.css` in the source code [#2265](https://github.com/ucsd-progsys/liquidhaskell/issues/2265)

## 0.9.6.3.1 (2024-03-07)

- Avoid enabling plugins in ghc-options (workaround for #9375)

## 0.9.6.3 (2024-01-29)

- Set support for GHC 9.6.3

## 0.9.4.7.0

- Set support for GHC 9.4.7

## 0.9.2.8.0

- Support for GHC 9.2.8
- Fix A normalization when type binder and lets are mixed in the input (#2236)
- Move KMeansHelper from liquid-prelude to tests

## 0.9.2.5

- Introduce package liquidhaskell-boot and eliminate wrapper packages for boot libraries
- List all definitions used from the GHC API
- Allow LH to verify modules in parallel (remove withArgs call)
- Remove some calls to HashMap.toList which caused some non-determinisms in different machines
- Implement a Haskell script to plot performance without gnuplot

## 0.9.0.2

- **breaking change** Remove the implicit types mechanism and corresponding tests
- **breaking change** Remove the `decrease` keyword and mechanism in favor of the terminating expressions syntax (`/ [a,b]`)

## 0.8.10.1

- Support for GHC 8.10.1
- LiquidHaskell is now available as a GHC Plugin

## 0.8.6.0

- Automatically check (transitive) dependencies
- Built with GHC 8.6.4
- Structural termination checker (on by default)
- Support for specifying class-laws and that they hold on instances
- Bug fixes for PLE
- Need to run LH on imported libs (with source) first; can use `--compile-spec` to avoid checking.

## 0.8.4.0

- Support for GHC 8.4.3
- Significant restructuring of `Bare` front-end to shrink dependency on GHC-API

## 0.8.2.2

- Support for GHC 8.2.2

- Support for GADTs and TypeFamilies, see
	- `tests/{pos,neg}/ExactGADT*.hs`

- Add support for Bags/Multisets, see
	- `tests/pos/bag.hs`
	- `tests/neg/bag.hs`
	- `tests/pos/ListISort-bag.hs`

- Add support for *inductive predicates* see
	- `tests/pos/IndEven.hs`
	- `tests/pos/IndPerm.hs`
	- `tests/pos/IndStar.hs`

## 0.8.0.1

- Support for GHC 8.0.2

## 0.7.0.1

- **DELETED** the gsDcons and generally carrying DataConP beyond Bare; this _may_ cause
  problems with `target` as I removed the `dconEnv` field in `TargetState`. Is it live?
  To restore: have to apply the substitution syms/su in Bare.hs ALSO to gsDconsP (after
  restoring the gsDconsP field to [(DataCon, DataConP)])


- **breaking change** Remove the `Bool` vs. `Prop` distinction. This means that:

    * signatures that use(d) `Prop` as a type, e.g.
      `foo :: Int -> Prop` should just be `foo :: Int -> Bool`.

    * refinements that use(d) `Prop v` e.g.
      `isNull :: xs:[a] -> {v:Bool | Prop v <=> len xs > 0}`
      should just be `isNull :: xs:[a] -> {v:Bool | v <=> len xs > 0}`.

- Add `--eliminate={none, some, all}`. Here
  * `none` means don't use eliminate at all, use qualifiers everywhere (old-style)
  * `some` which is the **DEFAULT**  -- means eliminate all the **non-cut** variables
  * `all`  means eliminate where you can, and solve *cut* variables to `True`.

- Change `--higherorder` so that it uses *only* the qualifiers obtained from
  type aliases (e.g. `type Nat = {v:Int | ... }`) and nothing else. This
  requires `eliminate=some`.

- Add a `--json` flag that runs in quiet mode where all output is
  suppressed and only the list of errors is returned as a JSON object to be
  consumed by an editor.

- Add `--checks` flag (formerly `--binders`), which checks a given binder's
  definition, assuming specified types for all callees (but inferring types for
  callees without signatures.)

- Add `--time-binds` which is like the above, but checks all binders in a module
  and prints out time taken for each.

## 0.5.0.1

- Fixed a bug in the specification for `Data.Traversable.sequence`
- Make interpreted mul and div the default, when `solver = z3`
- Use `--higherorder` to allow higher order binders into the fixpoint environment

## 0.5.0.0

- Added support for building with `stack`

- Added support for GHC 7.10 (in addition to 7.8)

- Added '--cabaldir' option that will automatically find a .cabal file in the ancestor
  path from which the target file belongs, and then add the relevant source and dependencies
  to the paths searched for by LiquidHaskell.

  This means we don't have to manually do `-i src` etc. when checking large projects,
  which can be tedious e.g. within emacs.


## 0.4.0.0

- Bounds as an alternative for logical constraints see `benchmarks/icfp15/pos/Overview.lhs`

## 0.3.0.0

- Logical constraints: add extra subtyping constraints to signatures, e.g.

    {-@
    (.) :: forall <p :: b -> c -> Prop, q :: a -> b -> Prop, r :: a -> c -> Prop>.
           {x::a, w::b<q x> |- c<p w> <: c<r x>}
           (y:b -> c<p y>)
        -> (z:a -> b<q z>)
        ->  x:a -> c<r x>
    @-}
    (.) f g x = f (g x)

- Inlining haskell functions as predicates and expressions, e.g.

    {-@ inline max @-}
    max x y = if x >= y then x else y

- Refining class instances. For example

    {-@ instance Compare Int where
        cmax :: Odd -> Odd -> Odd @-}

- Major restructuring of internal APIs

## 0.2.1.0
- Experimental support for lifting haskell functions to measures
If you annotate a Haskell function `foo` with {-@ measure foo @-}, LiquidHaskell will attempt to derive an equivalent measure from `foo`'s definition. This should help eliminate some boilerplate measures that used to be required.

## 0.2.0.0

- Move to GHC-7.8.3
LiquidHaskell now *requires* ghc-7.8.3.

- Termination
LiquidHaskell will now attempt to prove all recursive functions terminating. It tries to prove that some parameter (or combination thereof) decreases at each recursive callsite. By default, this will be the first parameter with an associated size measure (see Size Measures), but can be overridden with the `Decreases` annotation or a termination expression (see Termination Expressions).

If proving termination is too big of burden, it can be disabled on a per-module basis with the `--no-termination` flag, or on a per-function basis with the `Lazy` annotation.

- Size Measures
Data declarations now optionally take a *size measure*, which LiquidHaskell will use to prove termination of recursive functions. The syntax is:

    {-@ data List a [len] = Nil | Cons a (List a) @-}

- Termination Expressions
Termination Expressions can be used to specify the decreasing metric of a recursive function. They can be any valid LiquidHaskell expression and must be placed after the function's LiquidHaskell type, e.g.

    {-@ map :: (a -> b) -> xs:[a] -> [a] / [len xs] @-}

- Type Holes
To reduce the annotation burden, LiquidHaskell now accepts `_` as a placeholder for types and refinements. It can take the place of any base Haskell type and LiquidHaskell will query GHC to fill in the blanks, or it can take the place of a refinement predicate, in which case LiquidHaskell will infer an appropriate refinement. For example,

    {-@ add :: x:_ -> y:_ -> {v:_ | v = x + y} @-}
    add x y = x + y

becomes

    {-@ add :: Num a => x:a -> y:a -> {v:a | v = x + y} @-}
    add x y = x + y

- Assumed Specifications
The `assume` annotation now works as you might expect it to, i.e. LiquidHaskell will *not* verify that the implementation is correct. Furthermore, `assume` can be used to locally override the type of an imported function.

- Derived Measure Selectors
Given a data definition

    {-@ data Foo = Foo { bar :: Int, baz :: Bool } @-}

LiquidHaskell will automatically derive measures

    {-@ measure bar :: Foo -> Int @-}
    {-@ measure baz :: Foo -> Bool @-}

- Type-Class Specifications
LiquidHaskell can now verify prove that type-class instances satisfy a specification. Simply use the new `class` annotation

    {-@ class Num a where
          (+) :: x:a -> y:a -> {v:a | v = x + y}
          (-) :: x:a -> y:a -> {v:a | v = x - y}
          ...
      @-}

and LiquidHaskell will attempt to prove at each instance declaration that the implementations satisfy the class specification.

When defining type-class specifications you may find the need to use overloaded measures, to allow for type-specific definitions (see Type-Indexed Measures).

- Type-Indexed Measures
LiquidHaskell now accepts measures with *type-specific* definitions, e.g. a measure to describe the size of a value. Such measures are defined using the `class measure` syntax

    {-@ class measure size :: forall a. a -> Int @-}

and instances can be defined using the `instance measure` syntax, which mirrors the regular measure syntax

    {-@ instance measure size :: [a] -> Int
        size ([])   = 0
        size (x:xs) = 1 + size xs
      @-}
    {-@ instance measure size :: Tree a -> Int
        size (Leaf)       = 0
        size (Node l x r) = 1 + size l + size r
      @-}

- Parsing
We have greatly improved our parser to require fewer parentheses! Yay!

- Emacs/Vim Support
LiquidHaskell now comes with syntax checkers for [flycheck](https://github.com/flycheck/flycheck) in Emacs and [syntastic](https://github.com/scrooloose/syntastic) in Vim.

- Incremental Checking
LiquidHaskell has a new `--diffcheck` flag that will only check binders that have changed since the last run, which can drastically improve verification times.

- Experimental Support for Z3's theory of real numbers with the `--real` flag.
