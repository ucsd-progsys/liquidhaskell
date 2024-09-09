# `Assume reflect` specification

## Goal

This PR addresses #2126. The goal is to enable the addition of assumptions for the PLE system to unfold imported function definitions.

Let us take the example of `filter` from the standard library. We would like it to be reflected so that we can use it in the logic/specifications of our own files. Unfortunately, `filter` is defined outside our own code, so we cannot simply reflect it. Instead, we can provide our own definition of `filter`, called `myfilter` here, which will be used as the assumed definition of `filter` so that `filter` can be lifted.

Of course, this pragma is unsafe as it introduces a big assumption, since we could very well provide a function `myfiler` whose definition is completely different from `filter`. Yet PLE will assume they are the same.

## Syntax and use

### First, real-world example

```
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"    	@-}

module AssmRefl where

import Data.List (filter)

{-@ reflect myfilter @-}
myfilter :: (a -> Bool) -> [a] -> [a]
myfilter _pred []	= []
myfilter pred (x:xs)
  | pred x     	= x : myfilter pred xs
  | otherwise  	= myfilter pred xs

{-@ assume reflect filter as myfilter @-}

{-@ test :: p:(a -> Bool) -> { filter p [] == [] } @-}
test :: (a -> Bool) -> ()
test p = ()
```

### Basic use

The syntax for it is a LH comment of the form:

`{-@ assume reflect foobar as myfoobar @-}`

Where `foobar` is the opaque, imported function which is to be reflected. `myfoobar` is our definition of it.

Of course, `Mod.myfoobar` needs to exist in the logic, either via reflection or measure annotations. For instance, using:

`{-@ reflect myfoobar @-}`

LH will actually check that `myfoobar` is already reflected, if not, it will throw an error.

```haskell
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module AssmRefl where

foobar :: Int -> Bool 
foobar n = n `mod` 2 == 0

{-@ assume reflect foobar as myfoobar @-}
myfoobar :: Int -> Bool
myfoobar n = n `mod` 2 == 1

{-@ test :: { foobar 5 } @-} 
test :: ()
test = ()
```

```
tests/basic/pos/AssmRefl.hs:10:20: error:
    Cannot lift Haskell function `foobar` to logic
    "myfoobar" must be reflected first using {-@ reflect "myfoobar" @-}
```

### Reflection

Furthermore, we cannot `assume reflect` a function which has already been reflected. For instance, imagine that `filter` was actually reflected in `Data.List`. There would be no need for us to `assume reflect` it through our own definition, so we will also have an error if the original function is already reflected.

```haskell
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module AssmRefl where

{-@ reflect foobar @-}
foobar :: Int -> Bool 
foobar n = n `mod` 2 == 0

{-@ reflect myfoobar @-}
{-@ assume reflect foobar as myfoobar @-}
myfoobar :: Int -> Bool
myfoobar n = n `mod` 2 == 1

{-@ test :: { foobar 5 } @-} 
test :: ()
test = ()
```

```
tests/basic/pos/AssmRefl.hs:12:32: error:
    Cannot lift Haskell function `foobar` to logic
    Duplicate reflection of "foobar" defined at: tests/basic/pos/AssmRefl.hs:7:13-7:20 and "foobar" defined at: tests/basic/pos/AssmRefl.hs:12:32-12:39
```

### Type mismatch

Also, LH checks the type of `myfoobar` against the type of `foobar` so that at least we reject obviously wrong redefinitions, which do not even have the same type.

```haskell
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module AssmRefl where

foobar :: Int -> Bool 
foobar n = n `mod` 2 == 0

{-@ reflect myfoobar @-}
{-@ assume reflect foobar as myfoobar @-}
myfoobar :: Bool -> Bool
myfoobar n = True

{-@ test :: { foobar 5 } @-} 
test :: ()
test = ()
```

```
tests/basic/pos/AssmRefl.hs:11:20: error:
    Cannot lift Haskell function `foobar` to logic
    "AssmRefl.myfoobar" and "AssmRefl.foobar" should have the same type. But types GHC.Types.Bool -> GHC.Types.Bool and GHC.Types.Int -> GHC.Types.Bool do not match.
```

### Unsafety

As said previously, we can easily introduce falsity since we assume the definitions of both functions to be the same. So we can easily have something like:

```haskell
module AssmRefl where

alwaysFalse :: Bool 
alwaysFalse = False

{-@ reflect alwaysTrue @-}
{-@ assume reflect alwaysFalse as alwaysTrue @-}
alwaysTrue :: Bool
alwaysTrue = True

{-@ test :: { alwaysFalse } @-}
test :: ()
test = ()
```

Which is considered safe by LH. Indeed, it is up to the developer to know what they are doing at this point when making any `assume`.

### Multiple reflections

We disallow two (or more) redefinitions of a reflection inside the same module.

```haskell
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module AssmRefl where

alwaysFalse :: Bool 
alwaysFalse = False

{-@ reflect alwaysTrue @-}
{-@ assume reflect alwaysFalse as alwaysTrue @-}
alwaysTrue :: Bool
alwaysTrue = True

{-@ reflect alwaysFalse2 @-}
{-@ assume reflect alwaysFalse as alwaysFalse2 @-}
alwaysFalse2 :: Bool
alwaysFalse2 = False

{-@ test :: { alwaysFalse } @-} 
test :: ()
test = ()
```

```
tests/basic/pos/AssmRefl.hs:16:20: error:
	Cannot lift Haskell function `alwaysFalse` to logic
	Duplicate reflection of "alwaysFalse" defined at: tests/basic/pos/AssmRefl.hs:11:20-11:32 and "alwaysFalse" defined at: tests/basic/pos/AssmRefl.hs:16:20-16:32
```

### Imports
`assume reflect`s are imported in the current module and can be used in the logic.

```haskell
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module MyTest.ModFour where

foobar :: Int -> Bool
foobar n = n `mod` 2 <= 4

{-@ reflect myfoobar @-}
{-@ assume reflect foobar as myfoobar @-}
myfoobar :: Int -> Bool
myfoobar n = n `mod` 2 == 0
```

```haskell
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module MyTest.ModTwoA where

import MyTest.ModFour

{-@ mytest :: { foobar 4 } @-} 
mytest :: ()
mytest = ()
```

### Multiple imports
As is the case for `assumptions`, the imported `assume reflect`s are sorted in alphabetical order, since the fully qualified names are alphabetically sorted. Whence the last one alphabetically will shadow the other definitions, if any. Here, the one from `ModTwoB` shadows the one from `ModTwoA`.

```haskell
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module MyTest.ModTopLevel where

import MyTest.ModFour (foobar)
import MyTest.ModTwoA (myfoobar)
import MyTest.ModTwoB (myfoobar)

{-@ test :: { foobar 3 } @-}
test :: ()
test = ()
```

```haskell
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module MyTest.ModTwoB where
    
import MyTest.ModFour (foobar)

{-@ reflect myfoobar @-}
{-@ assume reflect foobar as myfoobar @-}
myfoobar :: Int -> Bool 
myfoobar n = n `mod` 2 == 1

{-@ mytest :: { foobar 5 } @-} 
mytest :: ()
mytest = ()
```

```haskell
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module MyTest.ModTwoA where

import MyTest.ModFour (foobar)

{-@ reflect myfoobar @-}
{-@ assume reflect foobar as myfoobar @-}
myfoobar :: Int -> Bool
myfoobar n = n `mod` 2 == 0

{-@ mytest :: { foobar 4 } @-} 
mytest :: ()
mytest = ()
```

```haskell
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module MyTest.ModFour where

foobar :: Int -> Bool
foobar n = n `mod` 2 <= 4
```

### Multiple reflections across modules

We allow redefinition of an imported `assume reflect`, that shadows the previously imported `assume reflect`s.

```haskell
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module MyTest.ModTopLevel where

import MyTest.ModFour (foobar)
import MyTest.ModTwoA (myfoobar)
import MyTest.ModTwoB (myfoobar)

{-@ assume reflect foobar as myfoobar3 @-}
{-@ reflect myfoobar3 @-}
myfoobar3 :: Int -> Bool
myfoobar3 n = n `mod` 2 == 0

{-@ test :: { foobar 2 } @-}
test :: ()
test = ()
```