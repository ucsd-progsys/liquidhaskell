# Introduction

This code commentary describes the current architecture for the GHC [Plugin][] that enables LiquidHaskell
to check files as part of the normal compilation process. For the sake of this commentary, we refer to
the code provided as part of the `release/0.8.10.2` branch, commit `9a2f8284c5fe5b18ed0410e842acd3329a629a6b`.

## GHC.Interface vs GHC.Plugin

The module [GHC.Plugin][] is the main entrypoint for all the plugin functionalities. Whenever possible, this
module is reusing common functionalities from the [GHC.Interface][], which is the original module used to
interface LH with the old executable. Generally speaking, the [GHC.Interface][] module is considered "legacy"
and it's rarely what one wants to modify. It will probably be removed once the old executable stops being
supported, with the functions now in use by the [GHC.Plugin][] being moved into the latter.

## The GhcMonadLike shim

Part of the tension in designing the plugin was trying to reuse as much code as possible from the original
[GHC.Interface][] shipped with LiquidHaskell. Unfortunately this was not possible from the get-go due to the
fact most of the functions provided by that module were requiring a [GhcMonad][] constraint or usually
living in the [Ghc monad][], which is also the only concrete type which derives an instance for [GhcMonad][].
While we could have run each and every function with `runGhc`, this was not very satisfactory due to the
fact running the `Ghc` monad is fairly expensive as it requires a bit of extra state in order to run it.

However, most of the functions used by the [Ghc.Interface][] didn't require anything specific from the
underlying [Ghc monad][] if not access to the [HscEnv][] and the ability to grab the [DynFlags][], as well
as doing `IO`. Therefore, the [GhcMonadLike][] shim was born with the intent of replicating some of the
functions used by the [GHC.Interface][] but crucially making those polymorphic in a generic [GhcMonadLike][]
for which we can give instances for `CoreM`, `TcM` etc. We can do this because we do not require the extra
`ExceptionMonad` constraint and we do not require to implement `setHscEnv`.

This allowed us to change ever so slightly the functions provided by the [GHC.Interface][], expose them and
reuse them in the [Plugin][] module.

## Plugin architecture

Broadly speaking, the Plugin is organised this way: In the [typechecking phase][], we typecheck and desugar
each module via the GHC API in order to extract the unoptimised [core binds][] that are needed by
LH to work correctly. This is due to a tension in the design space; from one side LH needs access to the
"raw" core binds (binds where primitives types are not unboxed in the presence of a PRAGMA annotation,
for example) but yet the user can specify any arbitrary optimisation settings during compilation and we do
not want to betray the principle of least expectation by silently compiling the code with `-O0`. Practically
speaking, this introduces some overhead and is far from ideal, but for now it allows us to iterate quickly.
This phase is also responsible for:

* Extracting the [BareSpec][]s associated to any of the dependent modules;
* Producing the [LiftedSpec][] for the currently-compiled module;
* Storing the [LiftedSpec][] into an interface annotation for later retrieval;
* Checking and verifying the module using LH's existing API.

The reason why we do everything in the [typechecking phase][] is also to allow integrations with tools like
[ghcide][]. There are a number of differences between the plugin and the operations performed as part of the
[GHC.Interface][], which we are going to outline in the next section.

## Differences with the GHC.Interface

- The [GHC.Interface][] pre-processes the input files and calls into [configureGhcTargets][] trying to
  build a dependency graph by discovering dependencies the target files might require. Then, from this
  list any file in the include directory is filtered out, as well as any module which has
  a "fresh" `.bspec` file on disk, to save time during checking. In the [GHC.Plugin][] module though
  we don't do this and for us, essentially, each input file is considered a target, where we exploit the
  fact GHC will skip recompilation if unnecessary. This also implies that while the [GHC.Interface][] calls
  into [processTargetModule][] only for target files, the [GHC.Plugin][] has a single, flat function simply
  called [processModule][] that essentially does the same as `GHC.Interface.processModule` and
  `GHC.Interface.processTargetModule` fused together.

- While the [GHC.Interface][] sometimes "assembles" a [BareSpec][] by mappending the `commSpec` (i.e. comment spec)
  with the [LiftedSpec][] fetched from disk, if any, the Plugin doesn't do this but rather piggybacks on the
  [SpecFinder][] (described later) to fetch dependencies' specs.

- There is a difference in how we process LIQUID pragmas. In particular, for the executable they seems to
  be accumulated "in bulk" i.e. if we are refining a *target* module `A` that depends on `B`, `B` seems to
  inherit whichever flags we were using in the *target* module `A`. Conversely, the source plugin is "stateless"
  when it comes to LIQUID options, i.e. it doesn't have memory of _past_ options, what it counts when compiling
  a module `B` is the _global_ options and _any_ option this module defines. The analogy is exactly the
  same as with GHC language extensions, they have either global scope (i.e. `default-extensions` in the
  cabal manifest) or local scope (i.e. `{-# LANGUAGE ... #-}`).

## Finding specs for existing modules

This is all done by a specialised module called the [SpecFinder][]. The main exported function is
[findRelevantSpecs][] which, given a list of `Module`s, tries to retrieve the `LiftedSpec`s associated with
them. Typically this is done by looking into the interface files of the input modules, trying to deserialise
any `LiftedSpec` from the interface file's annotations.

# FAQs

## Is it possible that the behaviour of the old executable and the new / the plugin differ?

It might happen, yes, but the surface area is fairly small. Both modules work by producing a [TargetSrc][]
that is passed to the internal LH API, which is shared by _both_ modules. Therefore, any difference in 
behaviour has to be researched in the code path that produces such [TargetSrc][]. For the [GHC.Plugin][] this
happens in the `makeTargetSrc`, whereas for the [GHC.Interface][] this happens inside the [makeGhcSrc][] function.

## Why is the GHC.Interface using slightly different types than the GHC.Plugin module?

Mostly for backward-compatibility and for historical reasons. Types like [BareSpec][] used to be type alias
rather than `newtype`s, and things were slightly renamed to reflect better purpose when the support for the
plugin was added. While doing so we also added a compat layer in the form of some `optics` that can be used
to map back and forth (sometimes in a partial way) between old and new data structures. When in doubt,
**consider the GHC.Plugin as the single source of truth, and prefer whichever data structure the latter is
using**.


[Plugin]:              https://github.com/ucsd-progsys/liquidhaskell/blob/9a2f8284c5fe5b18ed0410e842acd3329a629a6b/src/Language/Haskell/Liquid/GHC/Plugin.hs
[GHC.Plugin]:          https://github.com/ucsd-progsys/liquidhaskell/blob/9a2f8284c5fe5b18ed0410e842acd3329a629a6b/src/Language/Haskell/Liquid/GHC/Plugin.hs
[GHC.Interface]:       https://github.com/ucsd-progsys/liquidhaskell/blob/9a2f8284c5fe5b18ed0410e842acd3329a629a6b/src/Language/Haskell/Liquid/GHC/Interface.hs
[SpecFinder]:          https://github.com/ucsd-progsys/liquidhaskell/blob/9a2f8284c5fe5b18ed0410e842acd3329a629a6b/src/Language/Haskell/Liquid/GHC/Plugin/SpecFinder.hs
[BareSpec]:            https://github.com/ucsd-progsys/liquidhaskell/blob/9a2f8284c5fe5b18ed0410e842acd3329a629a6b/src/Language/Haskell/Liquid/Types/Specs.hs#L301
[LiftedSpec]:          https://github.com/ucsd-progsys/liquidhaskell/blob/9a2f8284c5fe5b18ed0410e842acd3329a629a6b/src/Language/Haskell/Liquid/Types/Specs.hs#L476
[TargetSrc]:           https://github.com/ucsd-progsys/liquidhaskell/blob/9a2f8284c5fe5b18ed0410e842acd3329a629a6b/src/Language/Haskell/Liquid/Types/Specs.hs#L160
[Ghc monad]:           https://hackage.haskell.org/package/ghc-8.10.1/docs/GHC.html#t:Ghc
[HscEnv]:              https://hackage.haskell.org/package/ghc-8.10.1/docs/GHC.html#t:HscEnv
[DynFlags]:            https://hackage.haskell.org/package/ghc-8.10.1/docs/GHC.html#t:DynFlags
[GhcMonad]:            https://hackage.haskell.org/package/ghc-8.10.1/docs/GHC.html#t:GhcMonad
[GhcMonadLike]:        https://github.com/ucsd-progsys/liquidhaskell/blob/9a2f8284c5fe5b18ed0410e842acd3329a629a6b/src/Language/Haskell/Liquid/GHC/GhcMonadLike.hs
[typechecking phase]:  https://github.com/ucsd-progsys/liquidhaskell/blob/9a2f8284c5fe5b18ed0410e842acd3329a629a6b/src/Language/Haskell/Liquid/GHC/Plugin.hs#L196-L224
[ghcide]:              https://github.com/haskell/ghcide
[findRelevantSpecs]:   https://github.com/ucsd-progsys/liquidhaskell/blob/9a2f8284c5fe5b18ed0410e842acd3329a629a6b/src/Language/Haskell/Liquid/GHC/Plugin/SpecFinder.hs#L61
[core binds]:          https://hackage.haskell.org/package/ghc-8.10.1/docs/CoreSyn.html#t:CoreBind
[configureGhcTargets]: https://github.com/ucsd-progsys/liquidhaskell/blob/9a2f8284c5fe5b18ed0410e842acd3329a629a6b/src/Language/Haskell/Liquid/GHC/Interface.hs#L268
[processTargetModule]: https://github.com/ucsd-progsys/liquidhaskell/blob/9a2f8284c5fe5b18ed0410e842acd3329a629a6b/src/Language/Haskell/Liquid/GHC/Interface.hs#L468
[processModule]:       https://github.com/ucsd-progsys/liquidhaskell/blob/9a2f8284c5fe5b18ed0410e842acd3329a629a6b/src/Language/Haskell/Liquid/GHC/Plugin.hs#L393
