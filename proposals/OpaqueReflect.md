# Specification of opaque reflection

This spec addresses #1892. The goal is to permit the reflection of functions which contain symbols that are not already in the logic, through the automatic lifting of the symbols which are not in the logic, as uninterpreted functions. In this document, we use "uninterpreted functions" and "measures" interchangeably.

The idea behind issue #1892 is that you may want to reflect a function without reflecting all the functions that are in the definition. For example, `Data.Map.lookup` may not be necessarily reflected for a function containing it to be reflected and reasoned about. Currently, the process of adding a dummy measure for functions we don't want to reflect is done manually and is often required. Such that it would be preferable to make opaque-reflection a default behavior, if no reflection is available for the symbol. In particular, because it allows the reflection of functions using imported symbols, that may not have been reflected there in the first place.

## Syntax and use

### First, real-world example

```Haskell
{-@ LIQUID "--reflection"      @-}

module OpaqueRefl04 where

{-@ reflect keepEvens @-}
keepEvens :: [Int] -> [Int]
keepEvens = filter even
```

It will introduce measures for `filter` and `even`, such that the result would be equivalent to

```Haskell
{-@ LIQUID "--reflection"      @-}

module OpaqueRefl06 where

{-@ measure GHC.Internal.List.filter :: (a -> Bool) -> [a] -> [a] @-}
{-@ assume GHC.Internal.List.filter :: p:(a -> Bool) -> xs:[a] -> {v : [a] | v == GHC.Internal.List.filter p xs && len v <= len xs} @-}
{-@ measure GHC.Internal.Real.even :: a -> GHC.Types.Bool @-}
{-@ assume GHC.Internal.Real.even :: x:a -> {VV : GHC.Types.Bool | VV == GHC.Internal.Real.even x} @-}

{-@ reflect keepEvens @-}
keepEvens :: [Int] -> [Int]
keepEvens = filter even
```

### Basic use

There is no specific syntax for opaque reflection. Instead, it takes place when doing reflection, i.e. with `{-@ reflect keepEvens @-}`. During reflection, the plugin goes through all the variables used in the definition of the function to reflect and looks for unlifted (= not present in the logic environment) free variables. In the precedent example, these free variables are `filter` and `even`.

For each unlifted free variable, it introduces a measure for it. For each measure introduced, we link the measure to the original function by strengthening the post-condition of the function, using the same pipeline as for reflection. We strengthen the post-condition by saying that the result `vv` is equal to the application of the measure to the arguments.

For instance,

```Haskell
{-@ assume GHC.List.filter :: p:(a -> GHC.Types.Bool) -> xs:[a] -> {v: [a] | len(v) <= len(xs) } @-}
```

Would become:

```Haskell
{-@ assume GHC.List.filter :: p:(a -> GHC.Types.Bool) -> xs:[a] -> {v: [a] | len(v) <= len(xs) && v = GHC.List.filter p xs} @-}
```

The measure can bear the same name as the original function, since the symbol was unbounded in the logic before (otherwise we would not perform opaque reflection in the first place). Whence `filter` in the post-condition truly refers to the measure and not the Haskell function.

If the user wishes to see what functions were opaque reflected, they can use the `--dump-opaque-reflections` pragma. It will list in the stdout the functions for which a measure was introduced automatically by opaque reflection. The functions are alphabetically ordered. An example output for the following code is:

```Haskell
{-@ LIQUID "--reflection"      @-}
{-@ LIQUID "--dump-opaque-reflections"      @-}

module OpaqueRefl06 where

{-@ reflect keepEvens @-}
keepEvens :: [Int] -> [Int]
keepEvens = filter even
```

```
Opaque reflections: 
- GHC.Internal.List.filter
- GHC.Internal.Real.even
```

### Postcondition
Strengthening the postcondition is useful to get lemmas for free and be able to reflect opaquely about those functions.

```Haskell
module OpaqueRefl05 where

import Data.Char (ord, chr)

{-@ reflect incChar @-}
incChar :: Char -> Char
incChar c = chr (ord c + 1)

{-@ ord' :: c:Char -> { v:Int | v = ord c } @-}
ord' :: Char -> Int
ord' c = ord c
```

### Multiple import example

If the same symbol is opaquely introduced in several modules, all instances of this opaque lifting are merged upon import.

```Haskell
{-@ LIQUID "--reflection" @-}

module OpaqueRefl03A where

import OpaqueRefl03B
import OpaqueRefl03C

myfoobar3 :: Int -> Int -> Int
myfoobar3 n m = myfoobar1 n m + myfoobar2 n m
```
```Haskell
{-@ LIQUID "--reflection" @-}

module OpaqueRefl03B where

import OpaqueRefl03D (foobar)

{-@ reflect myfoobar2 @-}
myfoobar2 :: Int -> Int -> Int
myfoobar2 n m = foobar n m
```

```Haskell
{-@ LIQUID "--reflection" @-}

module OpaqueRefl03C where

import OpaqueRefl03D (foobar)

{-@ reflect myfoobar1 @-}
myfoobar1 :: Int -> Int -> Int
myfoobar1 n m = foobar n m
```

```Haskell
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module OpaqueRefl03A where

import OpaqueRefl03B
import OpaqueRefl03C

{-@ reflect myfoobar3 @-}
myfoobar3 :: Int -> Int -> Int
myfoobar3 n m = myfoobar1 n m + myfoobar2 n m

{-@ usefulLemma :: n: Int -> m: Int -> {myfoobar3 n m == 2 * myfoobar1 n m} @-}
usefulLemma :: Int -> Int -> ()
usefulLemma n m = ()
```