---
layout: post
title: "Isomorphisms"
date: 2016-24-12 
author: Vikraman Choudhury 
published: false
comments: true
external-url:
categories: basic
demo: Iso.hs
---

\begin{comment}
\begin{code}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--totalhaskell" @-}
{-@ LIQUID "--exactdc" @-}
{-@ LIQUID "--diffcheck" @-}

module Iso where

import Language.Haskell.Liquid.ProofCombinators
\end{code}
\end{comment}

In this blog post, we show how to use Liquid Haskell to build "verified" typeclasses. A verified typeclass allows one to
express typeclass laws directly as Haskell code. We also show a technique to build verified instances and scale them up
to compound datatypes using isomorphisms.

First, we'll express verified typeclasses using Haskell records, but with LiquidHaskell refinements to express laws. As
an example, let's define `VerifiedOrd`, which is the same as the `Ord` typeclass, but with total order laws added.

\begin{code}
{-@ data VerifiedOrd a = VerifiedOrd {
      leq     :: a -> a -> Bool
    , refl    :: x:a -> { Prop (leq x x) }
    , antisym :: x:a -> y:a -> { Prop (leq x y) && Prop (leq y x) ==> x == y }
    , trans   :: x:a -> y:a -> z:a -> { Prop (leq x y) && Prop (leq y z) ==> Prop (leq x z) }
    , total   :: x:a -> y:a -> { Prop (leq x y) || Prop (leq y x) }
    }
@-}
data VerifiedOrd a = VerifiedOrd {
    leq     :: a -> a -> Bool
  , refl    :: a -> Proof
  , antisym :: a -> a -> Proof
  , trans   :: a -> a -> a -> Proof
  , total   :: a -> a -> Proof
}
\end{code}

The `leq` function represents the `<=` operator in `Ord`, and `refl`, `antisym`, `trans`, `total`, express the
reflexivity, antisymmetry, transitivity and totality properties respectively, that a total order requires. Notice how
the refinements express the laws, and the actual code is simply a function that returns `Proof` or `()`.

Now, let's see how to define some simple verified instances. We need to instantiate `leq` for our type, "reflect" it
into the logic, and prove all the required properties. For primitive types like `Int` or `Double`, it's "trivial"
because we trust the SMT solver which already knows about integers.

\begin{code}
{-@ axiomatize leqInt @-}
leqInt :: Int -> Int -> Bool
leqInt x y = x <= y

{-@ leqIntRefl :: x:Int -> { leqInt x x } @-}
leqIntRefl :: Int -> Proof
leqIntRefl x = leqInt x x ==. x <= x *** QED

{-@ leqIntAntisym :: x:Int -> y:Int -> { leqInt x y && leqInt y x ==> x == y } @-}
leqIntAntisym :: Int -> Int -> Proof
leqIntAntisym x y = (leqInt x y && leqInt y x) ==. (x <= y && y <= x) ==. x == y *** QED

{-@ leqIntTrans :: x:Int -> y:Int -> z:Int -> { leqInt x y && leqInt y z ==> leqInt x z } @-}
leqIntTrans :: Int -> Int -> Int -> Proof
leqIntTrans x y z = (leqInt x y && leqInt y z) ==. (x <= y && y <= z) ==. x <= z ==. leqInt x z *** QED

{-@ leqIntTotal :: x:Int -> y:Int -> { leqInt x y || leqInt y x } @-}
leqIntTotal :: Int -> Int -> Proof
leqIntTotal x y = (leqInt x y || leqInt y x) ==. (x <= y || y <= x) *** QED

vordInt :: VerifiedOrd Int
vordInt = VerifiedOrd leqInt leqIntRefl leqIntAntisym leqIntTrans leqIntTotal
\end{code}

How about a complex datatype? Let's consider an inductive datatype, the peano natural numbers. Not surprisingly, the
proofs follow by induction. For conciseness, we only show totality and elide the rest.

\begin{code}
{-@ data Peano [toNat] = Z | S Peano @-}
data Peano = Z | S Peano deriving (Eq)

{-@ measure toNat @-}
{-@ toNat :: Peano -> { n:Int | 0 <= n } @-}
toNat :: Peano -> Int
toNat Z = 0
toNat (S n) = 1 + toNat n

{-@ axiomatize leqPeano @-}
leqPeano :: Peano -> Peano -> Bool
leqPeano Z _ = True
leqPeano _ Z = False
leqPeano (S n) (S m) = leqPeano n m

{-@ leqNTotal :: n:Peano -> m:Peano -> {(leqPeano n m) || (leqPeano m n)} / [toNat n + toNat m] @-}
leqNTotal :: Peano -> Peano -> Proof
leqNTotal Z m = leqPeano Z m *** QED
leqNTotal n Z = leqPeano Z n *** QED
leqNTotal (S n) (S m)
  =   (leqPeano (S n) (S m) || leqPeano (S m) (S n))
  ==. (leqPeano n m || leqPeano (S m) (S n)) ? (leqNTotal n m )
  ==. (leqPeano n m || leqPeano m n) ? (leqNTotal m n)
  *** QED
\end{code}

Writing down proofs for more complex datatypes is tedious, it requires case analysis for each constructor and using the
induction hypothesis. However, we can decompose Haskell datatypes into sums and products, and we can build up compound
proofs using isomorphisms! To that end, we design some machinery to express isomorphisms, and prove that laws are
preserved under isomorphic images.

\begin{code}
{-@ data Iso a b = Iso {
      to   :: a -> b
    , from :: b -> a
    , tof  :: y:b -> { to (from y) == y }
    , fot  :: x:a -> { from (to x) == x }
    }
@-}
data Iso a b = Iso {
    to   :: a -> b
  , from :: b -> a
  , tof  :: b -> Proof
  , fot  :: a -> Proof
}
\end{code}

An isomorphism between types `a` and `b` is a pair of functions `to :: a -> b` and `from :: b -> a` that are mutually
inverse to each other. We now claim that total order laws are preserved under `Iso`; this amounts to building up a
`VerifiedOrd b`, given a `VerifiedOrd a` and an `Iso a b`.

\begin{code}
{-@ axiomatize leqFrom @-}
leqFrom :: (a -> a -> Bool)
        -> (b -> a)
        -> (b -> b -> Bool)
leqFrom leqa from x y = leqa (from x) (from y)

{-@ leqFromRefl :: leqa:(a -> a -> Bool) -> leqaRefl:(x:a -> { Prop (leqa x x) })
                -> from:(b -> a)
                -> x:b -> { leqFrom leqa from x x }
@-}
leqFromRefl :: (a -> a -> Bool) -> (a -> Proof)
            -> (b -> a)
            -> b -> Proof
leqFromRefl leqa leqaRefl from x =
      leqFrom leqa from x x
  ==. leqa (from x) (from x)
  ==. True ? leqaRefl (from x)
  *** QED

{-@ leqFromAntisym :: leqa:(a -> a -> Bool)
                   -> leqaAntisym:(x:a -> y:a -> { Prop (leqa x y) && Prop (leqa y x) ==> x == y })
                   -> to:(a -> b) -> from:(b -> a) -> tof:(y:b -> { to (from y) == y })
                   -> x:b -> y:b -> { leqFrom leqa from x y && leqFrom leqa from y x ==> x == y }
@-}
leqFromAntisym :: (Eq a, Eq b)
               => (a -> a -> Bool) -> (a -> a -> Proof)
               -> (a -> b) -> (b -> a) -> (b -> Proof)
               -> b -> b -> Proof
leqFromAntisym leqa leqaAntisym to from tof x y
  =   (leqFrom leqa from x y && leqFrom leqa from y x)
  ==. (leqa (from x) (from y) && leqa (from y) (from x))
  ==. from x == from y ? leqaAntisym (from x) (from y)
  ==. to (from x) == to (from y)
  ==. x == to (from y) ? tof x
  ==. x == y           ? tof y
  *** QED

{-@ leqFromTrans :: leqa:(a -> a -> Bool)
                 -> leqaTrans:(x:a -> y:a -> z:a -> { Prop (leqa x y) && Prop (leqa y z) ==> Prop (leqa x z) })
                 -> from:(b -> a)
                 -> x:b -> y:b -> z:b
                 -> { leqFrom leqa from x y && leqFrom leqa from y z ==> leqFrom leqa from x z }
@-}
leqFromTrans :: (a -> a -> Bool) -> (a -> a -> a -> Proof)
             -> (b -> a)
             -> b -> b -> b -> Proof
leqFromTrans leqa leqaTrans from x y z =
      (leqFrom leqa from x y && leqFrom leqa from y z)
  ==. (leqa (from x) (from y) && leqa (from y) (from z))
  ==. leqa (from x) (from z) ? leqaTrans (from x) (from y) (from z)
  ==. leqFrom leqa from x z
  *** QED

{-@ leqFromTotal :: leqa:(a -> a -> Bool) -> leqaTotal:(x:a -> y:a -> { Prop (leqa x y) || Prop (leqa y x) })
                 -> from:(b -> a) -> x:b -> y:b -> { leqFrom leqa from x y || leqFrom leqa from y x }
@-}
leqFromTotal :: (a -> a -> Bool) -> (a -> a -> Proof)
             -> (b -> a) -> b -> b -> Proof
leqFromTotal leqa leqaTotal from x y =
      (leqFrom leqa from x y || leqFrom leqa from y x)
  ==. (leqa (from x) (from y) || leqa (from y) (from x))
  ==. True ? leqaTotal (from x) (from y)
  ==. leqFrom leqa from y x
  *** QED

vordIso :: (Eq a, Eq b) => Iso a b -> VerifiedOrd a -> VerifiedOrd b
vordIso (Iso to from tof fot) (VerifiedOrd leqa leqaRefl leqaAntisym leqaTrans leqaTotal) =
  VerifiedOrd
    (leqFrom leqa from)
    (leqFromRefl leqa leqaRefl from)
    (leqFromAntisym leqa leqaAntisym to from tof)
    (leqFromTrans leqa leqaTrans from)
    (leqFromTotal leqa leqaTotal from)
\end{code}

We can now write a `VerifiedOrd` for `Peano` by mapping it onto `type Nat = { n:Int | 0 <= n }`, which is easier to
prove properties about because it's just an integer!

\begin{code}
{-@ type Nat = { n:Int | 0 <= n } @-}
type Nat = Int

{-@ axiomatize fromNat @-}
{-@ fromNat :: Nat -> Peano @-}
fromNat :: Nat -> Peano
fromNat n
  | n == 0 = Z
  | otherwise = S (fromNat (n - 1))

{-@ toFrom :: x:Nat -> { toNat (fromNat x) == x } @-}
toFrom :: Nat -> Proof
toFrom n
  | n == 0 = toNat (fromNat 0) ==. toNat Z ==. 0 *** QED
  | n > 0 = toNat (fromNat n)
        ==. toNat (S (fromNat (n - 1)))
        ==. 1 + toNat (fromNat (n - 1))
        ==. 1 + (n - 1) ? toFrom (n - 1)
        ==. n
        *** QED

{-@ fromTo :: x:Peano -> { fromNat (toNat x) == x } @-}
fromTo :: Peano -> Proof
fromTo Z = fromNat (toNat Z) ==. fromNat 0 ==. Z *** QED
fromTo (S n) = fromNat (toNat (S n))
           ==. fromNat (1 + toNat n)
           ==. S (fromNat ((1 + toNat n) - 1))
           ==. S (fromNat (toNat n))
           ==. S n ? fromTo n
           *** QED

{-@ isoNatPeano :: Iso Nat Peano @-}
isoNatPeano :: Iso Nat Peano
isoNatPeano = Iso fromNat toNat fromTo toFrom

vordNat :: VerifiedOrd Nat
vordNat = VerifiedOrd leqInt leqIntRefl leqIntAntisym leqIntTrans leqIntTotal

vordPeano :: VerifiedOrd Peano
vordPeano = vordIso isoNatPeano vordNat
\end{code}

Similarly, we can break down compound datatypes into sums and products, just like what happens in `GHC.Generics`, and
use the isomorphism to write down `VerifiedOrd` instances. We do however need to provide instances of `VerifiedOrd` for
sums and products.

\begin{code}
vordProd :: VerifiedOrd a -> VerifiedOrd b -> VerifiedOrd (a, b)
vordSum :: VerifiedOrd a -> VerifiedOrd b -> VerifiedOrd (Either a b)
\end{code}

\begin{comment}
\begin{code}
vordSum = undefined
vordProd = undefined
\end{code}
\end{comment}

Our [library](https://github.com/iu-parfunc/verified-instances) explores this idea to build some verified typeclasses,
such as `VerifiedOrd` and `VerifiedMonoid`. We also provide combinators to build verified instances by using
isomorphisms. Also, using a [reflection hack](https://www.schoolofhaskell.com/user/thoughtpolice/using-reflection), we
can reify these "verified" terms to typeclass dictionaries at runtime, to call legacy functions which require `Ord`
constraints and so on.
