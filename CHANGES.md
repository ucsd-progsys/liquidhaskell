# Changes

## Next

- Reject `ple` and `automatic-instances` annotations in modules that enable
  neither `--ple-local` nor `--ple`
  [#2737](https://github.com/ucsd-progsys/liquidhaskell/issues/2737)
  [#2739](https://github.com/ucsd-progsys/liquidhaskell/pull/2739)
- Emit the `autosize` measure under its resolved name, so constraints that
  mention it are no longer rejected as having a free variable
  [#2736](https://github.com/ucsd-progsys/liquidhaskell/issues/2736)
  [#2738](https://github.com/ucsd-progsys/liquidhaskell/pull/2738)
- Skip the termination metric of a recursive group whose decreasing parameters
  have different types, instead of building one the solver cannot sort check
  [#2736](https://github.com/ucsd-progsys/liquidhaskell/issues/2736)
  [#2738](https://github.com/ucsd-progsys/liquidhaskell/pull/2738)
- Count the fields of every autosized type in the `autosize` measure, so the
  size grows along the edges between mutually recursive types
  [#2736](https://github.com/ucsd-progsys/liquidhaskell/issues/2736)

## 0.9.14.1.1 (2026-06-04)

- Stop shadowing reflected signatures with assumed signatures
  [#2675](https://github.com/ucsd-progsys/liquidhaskell/pull/2675)
- Allow parenthesis in arguments to type aliases. Require type aliases to start with upper-case
  [#2674](https://github.com/ucsd-progsys/liquidhaskell/pull/2674)
- Add `--save-bfq-on-error` flag for liquidhaskell and include it in CI
  [#2648](https://github.com/ucsd-progsys/liquidhaskell/pull/2648)
- Migrate from cmdargs to base:System.Console.GetOpt
  [#2672](https://github.com/ucsd-progsys/liquidhaskell/pull/2672)
  [#2677](https://github.com/ucsd-progsys/liquidhaskell/pull/2677)
  [#2678](https://github.com/ucsd-progsys/liquidhaskell/pull/2678)
- Avoid name resolution errors in define annotations
  [#2604](https://github.com/ucsd-progsys/liquidhaskell/pull/2667)

## 0.9.14.1 (2026-05-06)

- Upgrade to GHC 9.14.1 [#2604](https://github.com/ucsd-progsys/liquidhaskell/pull/2604)
- Expand defines in define bodies, allowing defines to reference other defines [#2666](https://github.com/ucsd-progsys/liquidhaskell/pull/2666)
- Add `--modern` flag that bundles recommended defaults for new projects [#2637](https://github.com/ucsd-progsys/liquidhaskell/pull/2637)
- Rename `--exact-data-cons` to `--adt` and remove `--no-adt` [#2642](https://github.com/ucsd-progsys/liquidhaskell/pull/2642)
- Strengthen data constructor specs independently of `--adt` [#2628](https://github.com/ucsd-progsys/liquidhaskell/pull/2628)
- Always strengthen environment of case alternatives during constraint generation [#2642](https://github.com/ucsd-progsys/liquidhaskell/pull/2642)
- Only produce selectors for data constructors in use [#2642](https://github.com/ucsd-progsys/liquidhaskell/pull/2642)
- Reject conflicting selector types across constructors [#2642](https://github.com/ucsd-progsys/liquidhaskell/pull/2642)
- Add `--warn-on-term-holes` flag for typed holes support [#2486](https://github.com/ucsd-progsys/liquidhaskell/pull/2486)
- Add PLE sort-compatibility check for measure application [#2663](https://github.com/ucsd-progsys/liquidhaskell/pull/2663)
- Add Core pass to eliminate `(?)` operator after ANF [#2664](https://github.com/ucsd-progsys/liquidhaskell/pull/2664)
- Remove refinement type signature of `(?)` and document it [#2664](https://github.com/ucsd-progsys/liquidhaskell/pull/2664)
- Add support for fractional literals in the logic [#2619](https://github.com/ucsd-progsys/liquidhaskell/pull/2619)
- Add `Bool` embed always, regardless of imports [#2642](https://github.com/ucsd-progsys/liquidhaskell/pull/2642)
- Preserve dead bindings by marking Ids as exported [#2661](https://github.com/ucsd-progsys/liquidhaskell/pull/2661)
- Keep dependent binds in scope regardless of their types [#2627](https://github.com/ucsd-progsys/liquidhaskell/pull/2627)
- Fix LHAssumptions module lookup with `-plugin-package` [#2665](https://github.com/ucsd-progsys/liquidhaskell/pull/2665)
- Fix spurious invariant propagation for measures on type synonyms [#2660](https://github.com/ucsd-progsys/liquidhaskell/pull/2660)
- Fix polymorphic kvar type variable mismatch [#2649](https://github.com/ucsd-progsys/liquidhaskell/issues/2649) [#2651](https://github.com/ucsd-progsys/liquidhaskell/pull/2651)
- Fix shifted argument binding when lambda has fewer args than predicate [#2657](https://github.com/ucsd-progsys/liquidhaskell/pull/2657)
- Propagate abstract refinement predicates on parenthesized types [#2657](https://github.com/ucsd-progsys/liquidhaskell/pull/2657)
- Improve error messages for predicate arity mismatch and misplaced abstract refinement arguments [#2657](https://github.com/ucsd-progsys/liquidhaskell/pull/2657)
- Add constraint IDs to termination check error messages [#2659](https://github.com/ucsd-progsys/liquidhaskell/pull/2659)
- Add an indication of precedence to checkBind errors [#2631](https://github.com/ucsd-progsys/liquidhaskell/pull/2631)
- Remove stack support (stack.yaml removed) [#2616](https://github.com/ucsd-progsys/liquidhaskell/pull/2616)

## 0.9.12.2.1 (2026-01-14)

- Disable LH when collecting Haddock comments and the noBackend is set [#2611](https:://github.com/ucsd-progsys/liquidhaskell/pull/2611)
- Make assume reflect error sensitive to dflags [#2607](https:://github.com/ucsd-progsys/liquidhaskell/pull/2607)
- Add a flag to dump the a-normalized core [#2605](https:://github.com/ucsd-progsys/liquidhaskell/pull/2605)
- Show solutions of non-cut kvars in error messages [#2596](https:://github.com/ucsd-progsys/liquidhaskell/pull/2596)
- Remove question marks as a distinction of predicates from other expressions [#2595](https:://github.com/ucsd-progsys/liquidhaskell/pull/2595)
- Require braces when declaring qualifier [#2594](https:://github.com/ucsd-progsys/liquidhaskell/pull/2594)
- Retire implementation of gradual refinement types [#2588](https:://github.com/ucsd-progsys/liquidhaskell/pull/2588)
- Remove old versions of PLE [#2587](https:://github.com/ucsd-progsys/liquidhaskell/pull/2587)
- Add new syntax for indexed types (Ix instead of Prop) [#2586](https:://github.com/ucsd-progsys/liquidhaskell/pull/2586)
- Handle `ByteArray#` as int in the logic [#2581](https:://github.com/ucsd-progsys/liquidhaskell/pull/2581)
- Do not ignore user qualifiers when using `--reflection` [#2580](https:://github.com/ucsd-progsys/liquidhaskell/pull/2580)
- Add set cardinality support when using cvc5 [#2577](https:://github.com/ucsd-progsys/liquidhaskell/pull/2577)
- Support the finite field theory when using cvc5 [#2571](https:://github.com/ucsd-progsys/liquidhaskell/pull/2571) [#2614](https:://github.com/ucsd-progsys/liquidhaskell/pull/2614)
- Allow to qualify predicate aliases [#2566](https:://github.com/ucsd-progsys/liquidhaskell/pull/2566)
- Implement stratified types [#2559](https:://github.com/ucsd-progsys/liquidhaskell/pull/2559)
- Resolve occurrences of imported opaquely-reflected functions [#2548](https:://github.com/ucsd-progsys/liquidhaskell/pull/2548)
- Allow to qualify type aliases [#2550](https:://github.com/ucsd-progsys/liquidhaskell/pull/2550)
- Print the amount of checked constraints when verification fails [#2545](https:://github.com/ucsd-progsys/liquidhaskell/pull/2545)
- Fix SMT crashes on reflected functions on polymorphic data types [#2542](https://github.com/ucsd-progsys/liquidhaskell/pull/2542)
- Look for cvc5 before cvc4 [#2513](https://github.com/ucsd-progsys/liquidhaskell/pull/2513)
- Change `--cores` default to 1 [#2564](https://github.com/ucsd-progsys/liquidhaskell/pull/2564)

## 0.9.12.2 (2025-03-22)

- Simplify kvar solutions in fqout files [liquid-fixpoint#741](https://github.com/ucsd-progsys/liquid-fixpoint/pull/741).
- Upgrade ghc to 9.12.2 [#2474](https://github.com/ucsd-progsys/liquidhaskell/pull/2474).

## 0.9.10.1.2 (2025-03-06)

- Implement opaque reflection, a feature to allow reflecting functions which
  call to non-reflected functions [#2323](https://github.com/ucsd-progsys/liquidhaskell/pull/2323).
- Implement reflection from interface files, which can reflect functions from
  their unfoldings [#2326](https://github.com/ucsd-progsys/liquidhaskell/pull/2326).
  The feature is limited at the moment by the constraints that affect reflecting
  functions in general. But we hope it becomes more interesting as reflection is
  made more flexible.
- Operators in the logic cannot be shadowed locally anymore since
  [#2327](https://github.com/ucsd-progsys/liquidhaskell/pull/2327).
- Added a flag `--dump-pre-normalized-core` to show core before A normalization
  and constraint generation [#2336](https://github.com/ucsd-progsys/liquidhaskell/pull/2336).
- Augmented the context of error messages [#2350](https://github.com/ucsd-progsys/liquidhaskell/pull/2350).
- Add a new flag `--etabeta` to reason with lambdas in PLE [#2356](https://github.com/ucsd-progsys/liquidhaskell/pull/2356)
- Add a new flag `--dependentcase` to expand support for higher-order reasoning [#2384](https://github.com/ucsd-progsys/liquidhaskell/pull/2384)
- Add support for reflecting lambda expressions [#2465](https://github.com/ucsd-progsys/liquidhaskell/pull/2465).
- Enabling the LiquidHaskell plugin now enables `-fno-ignore-interface-pragmas` ([#2326](https://github.com/ucsd-progsys/liquidhaskell/pull/2326))
  and `-dkeep-comments` ([#2367](https://github.com/ucsd-progsys/liquidhaskell/pull/2367)).
- LiquidHaskell earned a new `--minimal` verbosity level as default that prints the banner with the
  amount of constraints checked ([#2395](https://github.com/ucsd-progsys/liquidhaskell/pull/2395)).
  This banner is now suppressed when the verbosity is set to `--quiet` ([#2391](https://github.com/ucsd-progsys/liquidhaskell/pull/2391)).
- Avoid reparsing and retypechecking when verifying modules [#2389](https://github.com/ucsd-progsys/liquidhaskell/pull/2389).
- Name resolution is done only when verifying a module. It is no longer done when
  importing it [#2169](https://github.com/ucsd-progsys/liquidhaskell/issues/2169). One
  side effect of this change is that LH can now pick up names in scope using import aliases
  in most places (but see [#2481](https://github.com/ucsd-progsys/liquidhaskell/issues/2481)).
- Allow to link Haskell definitions with logical primitives via `define` declarations [#2463](https://github.com/ucsd-progsys/liquidhaskell/pull/2463).
- CVC5 solver is now supported for all logical theories, including Sets/Bags [#2483](https://github.com/ucsd-progsys/liquidhaskell/pull/2483)

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
