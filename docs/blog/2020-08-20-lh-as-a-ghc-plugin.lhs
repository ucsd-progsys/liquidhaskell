---
layout: post
title: LiquidHaskell is a GHC Plugin
date: 2020-08-20
comments: true
author: Ranjit Jhala 
published: true
tags: basic
demo: refinements101.hs
---

<div class="hidden">
\begin{code}
module Plugin where

incr :: Int -> Int
incr x = x + 1
\end{code}
</div>

I enjoy working with LH. However, I'd be the very first to confess 
that it has been incredibly tedious to get to work on *existing* code 
bases, for various reasons.

1. LH ran *one file at a time*; it was a hassle to **systematically analyze** 
   all the modules in a single package.

2. LH had *no notion of packages*; it was impossible to **import specifications** 
   across packages.

3. LH had *no integration* with the standard compilation cycle; it was difficult 
   to get robust, **development-time feedback** using `ghci` based tools.

I'm delighted to announce the release of [LH version 0.8.10.2](http://ucsd-progsys.github.io/liquidhaskell/).

Thanks to the ingenuity and tireless efforts of our friends [Alfredo Di Napoli](http://www.alfredodinapoli.com/) 
and [Andres Loh](https://www.andres-loeh.de/) at [Well-Typed](http://www.well-typed.com/) this new version 
solves all three of the above problems in a single stroke, making it vastly simpler 
(dare I say, quite straightforward!) to run LH on your Haskell code.

<!-- more -->

Alfredo and Andres' key insight was that all the above problems could be solved if 
LH could be re-engineered as a [GHC Compiler Plugin](https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/extending_ghc.html#compiler-plugins) 
using hooks that GHC exposes to integrate external checkers during compilation.
I strongly encourage you to check out Alfredo's talk at the [Haskell Implementor's Workshop](https://icfp20.sigplan.org/details/hiw-2020-papers/1/Liquid-Haskell-as-a-GHC-Plugin) 
if you want to learn more about the rather non-trivial mechanics of how this plugin was engineered.
However, in this post, lets look at *how* and *why* to use the plugin, 
in particular, how the plugin lets us

1. Use GHC's dependency resolution to analyze entire packages with minimal recompilation;

2. Ship refined type specifications for old or new packages, and have them be verified at client code;

3. Use tools like `ghci` based IDE tooling (e.g. `ghcid` or `ghcide` to get interactive feedback),

all of which ultimately, I hope, make Liquid Haskell easier to use.

1. Analyzing Packages
---------------------

First, lets see a small "demo" of how to *use* the plugin to compile 
a small [`lh-plugin-demo`](https://github.com/ucsd-progsys/lh-plugin-demo) 
package with two modules

```haskell
module Demo.Lib where

{-@ type Pos = {v:Int | 0 < v} @-}

{-@ incr :: Pos -> Pos @-}
incr :: Int -> Int
incr x = x - 1
```

which defines a function `incr` that consumes and returns positive integers, and 

```haskell
module Demo.Client where

import Demo.Lib

bump :: Int -> Int
bump n = incr n
```

which imports `Demo.Lib` and uses `incr`.

### Updating `.cabal` to compile with the LH plugin

To "check" this code with LH we need only tell GHC to use it as a plugin, in two steps.

1. First, adding a dependency to LH in the `.cabal` file (or `package.yaml`) 

```
  build-depends:
      liquidhaskell >= 0.8.10
```

2. Second, tell GHC to use the plugin 

```
  ghc-options: -fplugin=LiquidHaskell
```

That's it. Now, everytime you (re-)build the code, GHC will _automatically_ 
run LH on the changed modules! If you use `stack` you may have to specify 
a few more dependencies, as shown in the `stack.yaml`; there are none needed 
if you use `cabal-v2`. If you clone the repo and run, e.g. `cabal v2-build` 
or `stack build` you'll get the following result, after the relevant dependencies 
are downloaded and built of course...

```
rjhala@khao-soi ~/r/lh-demo (main)> stack build
lh-plugin-demo> configure (lib)
Configuring lh-plugin-demo-0.1.0.0...
lh-plugin-demo> build (lib)
Preprocessing library for lh-plugin-demo-0.1.0.0..
Building library for lh-plugin-demo-0.1.0.0..
[1 of 2] Compiling Demo.Lib

**** LIQUID: UNSAFE ************************************************************

/Users/rjhala/research/lh-demo/src/Demo/Lib.hs:7:1: error:
    Liquid Type Mismatch
    .
    The inferred type
      VV : {v : GHC.Types.Int | v == x - 1}
    .
    is not a subtype of the required type
      VV : {VV : GHC.Types.Int | 0 < VV}
    .
    in the context
      x : {v : GHC.Types.Int | 0 < v}
  |
7 | incr x = x - 1
  | ^^^^^^^^^^^^^^
```

oops, of course that `(-)` should be a `(+)` if we want the output to also be *positive* so 
lets edit the code to

```haskell
incr x = x + 1
```

and now we get

```
rjhala@khao-soi ~/r/lh-plugin-demo (main)> stack build
lh-plugin-demo> configure (lib)
Configuring lh-plugin-demo-0.1.0.0...

lh-plugin-demo> build (lib)
Preprocessing library for lh-plugin-demo-0.1.0.0..
Building library for lh-plugin-demo-0.1.0.0..
[1 of 2] Compiling Demo.Lib

**** LIQUID: SAFE (2 constraints checked) *****************************
[2 of 2] Compiling Demo.Client

**** LIQUID: UNSAFE ***************************************************

/Users/rjhala/lh-plugin-demo/src/Demo/Client.hs:6:15: error:
    Liquid Type Mismatch
    .
    The inferred type
      VV : {v : GHC.Types.Int | v == n}
    .
    is not a subtype of the required type
      VV : {VV : GHC.Types.Int | 0 < VV}
    .
    in the context
      n : GHC.Types.Int
  |
6 | bump n = incr n
  |               ^
```

That is, during the build, LH complains that `incr` is being called with a value `n` 
that is not strictly positive as required by `incr`. To fix the code, we can edit it 
in various ways, e.g. to only call `incr` if `n > 0`

```haskell
bump n 
  | n > 0     = incr n
  | otherwise = 0
```

and now the code builds successfully

```
rjhala@khao-soi ~/r/lh-plugin-demo (main)> stack build
lh-plugin-demo> configure (lib)
Configuring lh-plugin-demo-0.1.0.0...
lh-plugin-demo> build (lib)
Preprocessing library for lh-plugin-demo-0.1.0.0..
Building library for lh-plugin-demo-0.1.0.0..
[2 of 2] Compiling Demo.Client

**** LIQUID: SAFE (2 constraints checked) ****************************
lh-plugin-demo> copy/register
Installing library in ... 
Registering library for lh-plugin-demo-0.1.0.0..
```

### Benefits

There are a couple of benefits to note immediately

+ A plain `stack build` or `cabal v2-build` takes care of all the installing _and_ checking!

+ No need to separately _install_ LH; its part of the regular build.

+ GHC's recompilation machinery ensures that only the relevant 
  modules are checked, e.g. the second time round, LH did not need 
  to analyze `Lib.hs` only `Client.hs`

2. Shipping Specifications with Packages
----------------------------------------

While the above is nice, in principle it could have been done 
with some clever `makefile` trickery (perhaps?). What I'm much 
more excited about is that now, for the first time, you can 
*ship refinement type specifications within plain Haskell packages*.

For example, consider a different [lh-plugin-demo-client](https://github.com/ucsd-progsys/lh-plugin-demo-client) 
package that uses `incr` from `lh-plugin-demo`:

```haskell
bump :: Int -> Int
bump n
  | n > 0     = incr n
  | otherwise = incr (0 - n)
```

Again, the `lh-plugin-demo-client.cabal` file need only specify the various 
dependencies:

```
  build-depends:
      liquidhaskell,
      lh-plugin-demo
````

and that GHC should use the plugin

```
  ghc-options: -fplugin=LiquidHaskell
```

and lo! a plain `stack build` or `cabal v2-build` takes care of all the rest.

```
rjhala@khao-soi ~/r/lh-plugin-demo-client (main)> stack build
lh-plugin-demo-client> configure (lib)
Configuring lh-plugin-demo-client-0.1.0.0...

lh-plugin-demo-client> build (lib)
Preprocessing library for lh-plugin-demo-client-0.1.0.0..
Building library for lh-plugin-demo-client-0.1.0.0..
[1 of 1] Compiling Demo.ExternalClient

**** LIQUID: UNSAFE ****************************************************

/Users/rjhala/lh-plugin-demo-client/src/Demo/ExternalClient.hs:8:22: error:
    Liquid Type Mismatch
    .
    The inferred type
      VV : {v : GHC.Types.Int | v == 0 - n}
    .
    is not a subtype of the required type
      VV : {VV : GHC.Types.Int | VV > 0}
    .
    in the context
      n : GHC.Types.Int
  |
8 |   | otherwise = incr (0 - n)
  |                      ^^^^^^^
```

(Whoops another off by one error, lets fix it!)

```haskell
bump :: Int -> Int
bump n
  | n > 0     = incr n
  | otherwise = incr (1 - n)
```

and now all is well

```
rjhala@khao-soi ~/r/lh-plugin-demo-client (main)> stack build --fast
lh-plugin-demo-client> configure (lib)
Configuring lh-plugin-demo-client-0.1.0.0...
lh-plugin-demo-client> build (lib)
Preprocessing library for lh-plugin-demo-client-0.1.0.0..
Building library for lh-plugin-demo-client-0.1.0.0..
[1 of 1] Compiling Demo.ExternalClient

**** LIQUID: SAFE (3 constraints checked) *****************************

lh-plugin-demo-client> copy/register
Installing library in ... 
Registering library for lh-plugin-demo-client-0.1.0.0..
```

### Prelude Specifications

Did you notice the strange `liquid-base` dependency in the cabal files? 

Previously, LH came installed with a "built-in" set of specifications for 
various `prelude` modules. This was _hacked_ inside LH in a rather unfortunate 
manner, which made these specifications very difficult to extend. 

Moving forward, all the refinement specifications e.g. for `GHC.List` or `Data.Vector` 
or `Data.Set` or `Data.Bytestring` simply live in packages that *mirror* the original 
versions, e.g. `liquid-base`,  `liquid-vector`, `liquid-containers`, `liquid-bytestring`.
Each `liquid-X` package directly _re-exports_ all the contents of the corresponding `X` package,
but with any additional refinement type specifications. 

So if you want to verify that _your_ code has no `vector`-index overflow errors, you simply 
build with `liquid-vector` instead of `vector`! Of course, in an ideal, and hopefully 
not too distant future, we'd get the refinement types directly inside `vector`, `containers` 
or `bytestring`.

### Benefits

So to recap, the plugin offers several nice benefits with respect to *shipping specifications*

* Refined signatures are bundled together with packages,

* Importing packages with refined signatures automatically ensures those signatures are 
  checked on client code,
  
* You can (optionally) use refined versions of `prelude` signatures, and hence, even 
  write refined versions of your favorite *custom preludes*.

3. Editor Tooling
-----------------

I saved _my_ favorite part for the end.

What I have enjoyed the most about the plugin is that now (almost) all the GHC-based 
tools that I use in my regular Haskell development workflow, automatically incorporate 
LH too! For example, reloading a module in `ghci` automatically re-runs LH on that file.

### `ghcid`

This means, that the mega robust, editor-independent `ghcid` now automatically 
produces LH type errors when you save a file. Here's `ghcid` running in a terminal.

![ghcid](/static/img/plugin-ghcid.gif)

### `vscode`

Editor plugins now produce little red squiggles for LH errors too.
Here's `code` with the `Simple GHC (Haskell) Integration` plugin

![](/static/img/plugin-vscode.gif)

### `emacs`

Here's `doom-emacs` with the `dante` plugin 

![](/static/img/plugin-emacs.gif)

### `vim`

And here is `neovim` with `ALE` and the `stack-build` linter

![](/static/img/plugin-vim.png)

### Benefits

+ Some of this _was_ possible before: we had to write special LH modes for different 
  editors. However, now we can simply work with the increasingly more robust GHCi and 
  Language-Server based tools already available for major editors and IDEs.

4. Caveats
----------

Of course, all the above is quite new, and so there are a few things to watch out for.

* First, for certain kinds of code, LH can take much longer than GHC to check a file.
  This means, it may actually be too slow to run on every save, and you may want to 
  tweak your `.cabal` file to *only* run the plugin during particular builds, not on 
  every file update.

* Second, the `liquid-X` machinery is designed to allow drop in replacements for various 
  base packages; it appears to work well in our testing, but if you try it, do let us know 
  if you hit some odd problems that we may not have anticipated.


Summary
-------

Hopefully the above provides an overview of the new plugin mode: how it can be used,
and what things it enables. In particular, by virtue of being a GHC plugin, LH can now

1. Run on entire Haskell packages;

2. Export and import specifications across packages;

3. Provide errors via existing GHC/i based editor tooling. 

All of which, I hope, makes it a lot easier to run LH on your code.

Our most profound thanks to the [National Science Foundation](https://nsf.gov/): 
this work was made possible by the support provided by grant 1917854: 
"FMitF: Track II: Refinement Types in the Haskell Ecosystem".
