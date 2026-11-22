{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--fuel=4" @-}

module TruePositives where

import Prelude hiding (map, take)
import Language.Haskell.Liquid.ProofCombinators (Proof, (?), (===), (***), QED(..))

--------------------------------------------------------------------------------
-- Common definitions
--------------------------------------------------------------------------------

{-@ type Nat = {v:Int | v >= 0} @-}
type Nat = Int

{-@ reflect compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

--------------------------------------------------------------------------------
-- Infinite streams (inductive encoding with IStream refinement)
--------------------------------------------------------------------------------

data Stream a = (:>) { shead :: a, stail :: Stream a } | StreamEnd

infixr 5 :>

{-@ measure isCons @-}
isCons :: Stream a -> Bool
isCons (_ :> _)  = True
isCons StreamEnd = False

{-@ type IStream a = {v:Stream a | isCons v} @-}
{-@ data Stream a = (:>) { shead :: a, stail :: IStream a } | StreamEnd @-}

--------------------------------------------------------------------------------
-- Indexed stream equality & extensionality scaffolding
--------------------------------------------------------------------------------

{-@ reflect eqK @-}
{-@ eqK :: Eq a => IStream a -> IStream a -> k:Nat -> Bool / [k] @-}
eqK :: Eq a => Stream a -> Stream a -> Int -> Bool
eqK _ _ 0 = True
eqK (x :> xs) (y :> ys) k =
  x == y && eqK xs ys (k - 1)

{-@
eqCons
  :: Eq a
  => x:IStream a
  -> k:{Nat | k > 0}
  -> y:IStream a
  -> {v:Proof | shead x == shead y}
  -> {v:Proof | eqK (stail x) (stail y) (k - 1)}
  -> {eqK x y k}
@-}
eqCons :: Eq a => Stream a -> Int -> Stream a -> Proof -> Proof -> Proof
eqCons (_ :> _) _ (_ :> _) _ _ = ()

{-@ reflect take @-}
{-@ take :: k:Nat -> IStream a -> [a] / [k] @-}
take :: Int -> Stream a -> [a]
take 0 _ = []
take k (x :> xs) = x : take (k - 1) xs

{-@
eqKLemma
  :: Eq a
  => x:IStream a
  -> y:IStream a
  -> k:Nat
  -> {eqK x y k <=> take k x == take k y}
  / [k]
@-}
eqKLemma :: Eq a => Stream a -> Stream a -> Int -> Proof
eqKLemma _ _ 0 = ()
eqKLemma (_ :> xs) (_ :> ys) k =
  eqKLemma xs ys (k - 1)

{-@
assume takeLemma
  :: x:IStream a
  -> y:IStream a
  -> (k:Nat -> {take k x == take k y})
  -> {x == y}
@-}
takeLemma :: Stream a -> Stream a -> (Int -> Proof) -> Proof
takeLemma _ _ _ = ()

{-@
approx
  :: Eq a
  => x:IStream a
  -> y:IStream a
  -> (k:Nat -> {eqK x y k})
  -> {x == y}
@-}
approx :: Eq a => Stream a -> Stream a -> (Int -> Proof) -> Proof
approx x y p =
  takeLemma x y (\k -> eqKLemma x y k ? p k)

{-@ lazy smap @-}
{-@ reflect smap @-}
{-@ smap :: (a -> b) -> IStream a -> IStream b @-}
smap :: (a -> b) -> Stream a -> Stream b
smap f (x :> xs) = f x :> smap f xs

--------------------------------------------------------------------------------
-- 1. Map fusion on streams
--
-- Sources:
--   Mastorou, Papaspyrou, and Vazou (2022), Coinduction Inductively.
--
-- EXPECTED: ACCEPT (INDEXED COINDUCTIVE PROOF).
--
-- Proves smap f (smap g xs) == smap (compose f g) xs by induction on the
-- observation depth k, then lifts to stream equality via approx.
--------------------------------------------------------------------------------

{-@ composeDef :: f:(b -> c) -> g:(a -> b) -> x:a -> {compose f g x == f (g x)} @-}
composeDef :: (b -> c) -> (a -> b) -> a -> Proof
composeDef _ _ _ = ()

{-@
mapFusionK
  :: Eq c
  => f:(b -> c)
  -> g:(a -> b)
  -> s:IStream a
  -> k:Nat
  -> {eqK (smap f (smap g s)) (smap (compose f g) s) k}
  / [k]
@-}
mapFusionK
  :: Eq c
  => (b -> c)
  -> (a -> b)
  -> Stream a
  -> Int
  -> Proof
mapFusionK _ _ _ 0 = ()
mapFusionK f g s@(x :> xs) k =
  eqCons
    (smap f (smap g s))
    k
    (smap (compose f g) s)
    (composeDef f g x)
    (mapFusionK f g xs (k - 1))

{-@
mapFusion
  :: Eq c
  => f:(b -> c)
  -> g:(a -> b)
  -> xs:IStream a
  -> {smap f (smap g xs) == smap (compose f g) xs}
@-}
mapFusion
  :: Eq c
  => (b -> c)
  -> (a -> b)
  -> Stream a
  -> Proof
mapFusion f g xs =
  approx
    (smap f (smap g xs))
    (smap (compose f g) xs)
    (mapFusionK f g xs)

--------------------------------------------------------------------------------
-- 2. Merging odds and evens reconstructs the original stream
--
-- Sources:
--   Mastorou, Papaspyrou, and Vazou (2022), Coinduction Inductively.
--
-- EXPECTED: ACCEPT (INDEXED COINDUCTIVE PROOF).
--
-- Proves merge (odds xs) (evens xs) == xs by induction on k and lifting via
-- approx.
--------------------------------------------------------------------------------

{-@ lazy merge @-}
{-@ reflect merge @-}
{-@ merge :: IStream a -> IStream a -> IStream a @-}
merge :: Stream a -> Stream a -> Stream a
merge (x :> xs) ys = x :> merge ys xs

{-@ lazy odds @-}
{-@ reflect odds @-}
{-@ odds :: IStream a -> IStream a @-}
odds :: Stream a -> Stream a
odds (x :> (_ :> xs)) = x :> odds xs

{-@ reflect evens @-}
{-@ evens :: IStream a -> IStream a @-}
evens :: Stream a -> Stream a
evens (_ :> xs) = odds xs

{-@
mergeEvenOddK
  :: Eq a
  => xs:IStream a
  -> k:Nat
  -> {eqK (merge (odds xs) (evens xs)) xs k}
  / [k]
@-}
mergeEvenOddK :: Eq a => Stream a -> Int -> Proof
mergeEvenOddK _ 0 = ()
mergeEvenOddK xs@(_ :> ys@(_ :> _)) k =
  eqCons
    (merge (odds xs) (evens xs))
    k
    xs
    ()
    (mergeEvenOddK ys (k - 1))

{-@
mergeEvenOdd
  :: Eq a
  => xs:IStream a
  -> {merge (odds xs) (evens xs) == xs}
@-}
mergeEvenOdd :: Eq a => Stream a -> Proof
mergeEvenOdd xs =
  approx
    (merge (odds xs) (evens xs))
    xs
    (mergeEvenOddK xs)

--------------------------------------------------------------------------------
-- 3. Thue-Morse sequence is a fixed point of f
--
-- Sources:
--   Mastorou, Papaspyrou, and Vazou (2022), Coinduction Inductively.
--
-- EXPECTED: ACCEPT (INDEXED COINDUCTIVE PROOF).
--
-- Proves f morse == morse using the auxiliary indexed lemma fMergeK and
-- lifting via approx.
--------------------------------------------------------------------------------

{-@ reflect bnot @-}
bnot :: Bool -> Bool
bnot True  = False
bnot False = True

{-@ lazy morse @-}
{-@ reflect morse @-}
{-@ morse :: IStream Bool @-}
morse :: Stream Bool
morse =
  False :> (True :> merge
    (stail morse)
    (smap bnot (stail morse)))

{-@ morseSecondHead
        :: {shead (stail (f morse)) == shead (stail morse)}
@-}
morseSecondHead :: Proof
morseSecondHead = ()

{-@ morseTail2
        :: {stail (stail morse)
                == merge (stail morse) (smap bnot (stail morse))}
@-}
morseTail2 :: Proof
morseTail2 = ()

{-@ lazy f @-}
{-@ reflect f @-}
{-@ f :: IStream Bool -> IStream Bool @-}
f :: Stream Bool -> Stream Bool
f (x :> xs) =
    x :> (bnot x :> f xs)

{-@ fMergeHead
        :: s:IStream Bool
        -> {shead (f s) == shead (merge s (smap bnot s))}
@-}
fMergeHead :: Stream Bool -> Proof
fMergeHead s@(x :> xs)
  =   shead (f s)
  === shead (x :> (bnot x :> f xs))
  === x
  === shead (x :> merge (smap bnot s) xs)
  === shead (merge s (smap bnot s))
  *** QED

{-@ fMergeSecond
        :: s:IStream Bool
        -> {shead (stail (f s)) == shead (stail (merge s (smap bnot s)))}
@-}
fMergeSecond :: Stream Bool -> Proof
fMergeSecond s@(x :> xs)
  =   shead (stail (f s))
  === shead (stail (x :> (bnot x :> f xs)))
  === bnot x
  === shead (bnot x :> merge xs (smap bnot xs))
  === shead (merge (bnot x :> smap bnot xs) xs)
  === shead (merge (smap bnot s) xs)
  === shead (stail (x :> merge (smap bnot s) xs))
  === shead (stail (merge s (smap bnot s)))
  *** QED

{-@ fMergeTail
        :: s:IStream Bool
        -> {stail (stail (f s)) == f (stail s)}
@-}
fMergeTail :: Stream Bool -> Proof
fMergeTail (_ :> _) = ()

{-@ mergeBnotTail
        :: s:IStream Bool
        -> {stail (stail (merge s (smap bnot s)))
                == merge (stail s) (smap bnot (stail s))}
@-}
mergeBnotTail :: Stream Bool -> Proof
mergeBnotTail s@(x :> xs)
  =   stail (stail (merge s (smap bnot s)))
  === stail (stail (x :> merge (smap bnot s) xs))
  === stail (merge (smap bnot s) xs)
  === stail (merge (bnot x :> smap bnot xs) xs)
  === stail (bnot x :> merge xs (smap bnot xs))
  === merge xs (smap bnot xs)
  === merge (stail s) (smap bnot (stail s))
  *** QED

{-@
fMergeK
        :: s:IStream Bool
        -> k:Nat
        -> {eqK (f s) (merge s (smap bnot s)) k}
        / [k]
@-}
fMergeK :: Stream Bool -> Int -> Proof
fMergeK _ 0 = ()
fMergeK s@(_ :> _) 1 =
  eqCons
    (f s)
    1
    (merge s (smap bnot s))
    (fMergeHead s)
    ()
fMergeK s@(_ :> xs@(_ :> _)) k =
  eqCons
    (f s)
    k
    (merge s (smap bnot s))
    (fMergeHead s)
    (eqCons
      (stail (f s))
      (k - 1)
      (stail (merge s (smap bnot s)))
      (fMergeSecond s)
      (fMergeTail s
        ? mergeBnotTail s
        ? fMergeK xs (k - 2)))

{-@
morseFixK
        :: k:Nat
        -> {eqK (f morse) morse k}
        / [k]
@-}
morseFixK :: Int -> Proof
morseFixK 0 = ()
morseFixK 1 = ()
morseFixK k =
  eqCons
    (f morse)
    k
    morse
    ()
    (eqCons
      (stail (f morse))
      (k - 1)
      (stail morse)
      morseSecondHead
      (fMergeTail morse
        ? morseTail2
        ? fMergeK (stail morse) (k - 2)))

{-@
morseFix
        :: {f morse == morse}
@-}
morseFix :: Proof
morseFix =
  approx (f morse) morse morseFixK

--------------------------------------------------------------------------------
-- 4. Commutativity of f with pointwise Boolean negation
--
-- Sources:
--   Mastorou, Papaspyrou, and Vazou (2022), Coinduction Inductively.
--
-- EXPECTED: ACCEPT (INDEXED COINDUCTIVE PROOF).
--
-- Proves f (smap bnot xs) == smap bnot (f xs) by step-2 induction on k and
-- lifting via approx.
--------------------------------------------------------------------------------

{-@ fNotHead
        :: s:IStream Bool
        -> {shead (f (smap bnot s))
                == shead (smap bnot (f s))}
@-}
fNotHead :: Stream Bool -> Proof
fNotHead s@(x :> xs)
  =   shead (f (smap bnot s))
  === shead (f (bnot x :> smap bnot xs))
  === shead (bnot x :> (bnot (bnot x) :> f (smap bnot xs)))
  === bnot x
  === shead (bnot x :> smap bnot (bnot x :> f xs))
  === shead (smap bnot (x :> (bnot x :> f xs)))
  === shead (smap bnot (f s))
  *** QED

{-@ fNotSecond
        :: s:IStream Bool
        -> {shead (stail (f (smap bnot s)))
                == shead (stail (smap bnot (f s)))}
@-}
fNotSecond :: Stream Bool -> Proof
fNotSecond s@(x :> xs)
  =   shead (stail (f (smap bnot s)))
  === shead (stail (f (bnot x :> smap bnot xs)))
  === shead (stail (bnot x :> (bnot (bnot x) :> f (smap bnot xs))))
  === bnot (bnot x)
  === shead (bnot (bnot x) :> smap bnot (f xs))
  === shead (smap bnot (bnot x :> f xs))
  === shead (stail (bnot x :> smap bnot (bnot x :> f xs)))
  === shead (stail (smap bnot (x :> (bnot x :> f xs))))
  === shead (stail (smap bnot (f s)))
  *** QED

{-@ fNotTailLeft
        :: s:IStream Bool
        -> {stail (stail (f (smap bnot s)))
                == f (smap bnot (stail s))}
@-}
fNotTailLeft :: Stream Bool -> Proof
fNotTailLeft s@(x :> xs)
  =   stail (stail (f (smap bnot s)))
  === stail (stail (f (bnot x :> smap bnot xs)))
  === stail (stail (bnot x :> (bnot (bnot x) :> f (smap bnot xs))))
  === f (smap bnot xs)
  === f (smap bnot (stail s))
  *** QED

{-@ fNotTailRight
        :: s:IStream Bool
        -> {stail (stail (smap bnot (f s)))
                == smap bnot (f (stail s))}
@-}
fNotTailRight :: Stream Bool -> Proof
fNotTailRight s@(x :> xs)
  =   stail (stail (smap bnot (f s)))
  === stail (stail (smap bnot (x :> (bnot x :> f xs))))
  === stail (stail (bnot x :> smap bnot (bnot x :> f xs)))
  === stail (smap bnot (bnot x :> f xs))
  === stail (bnot (bnot x) :> smap bnot (f xs))
  === smap bnot (f xs)
  === smap bnot (f (stail s))
  *** QED

{-@
fNotCommuteK
        :: s:IStream Bool
        -> k:Nat
        -> {eqK (f (smap bnot s)) (smap bnot (f s)) k}
        / [k]
@-}
fNotCommuteK :: Stream Bool -> Int -> Proof
fNotCommuteK _ 0 = ()
fNotCommuteK s@(_ :> _) 1 =
  eqCons
    (f (smap bnot s))
    1
    (smap bnot (f s))
    (fNotHead s)
    ()
fNotCommuteK s@(_ :> xs@(_ :> _)) k =
  eqCons
    (f (smap bnot s))
    k
    (smap bnot (f s))
    (fNotHead s)
    (eqCons
      (stail (f (smap bnot s)))
      (k - 1)
      (stail (smap bnot (f s)))
      (fNotSecond s)
      (fNotTailLeft s
        ? fNotTailRight s
        ? fNotCommuteK xs (k - 2)))

{-@
fNotCommute
        :: xs:IStream Bool
        -> {f (smap bnot xs) == smap bnot (f xs)}
@-}
fNotCommute :: Stream Bool -> Proof
fNotCommute xs =
  approx
    (f (smap bnot xs))
    (smap bnot (f xs))
    (fNotCommuteK xs)

--------------------------------------------------------------------------------
-- 5. Trivial unary stream predicate holds for every stream
--
-- Sources:
--   Mastorou, Papaspyrou, and Vazou (2022), Coinduction Inductively.
--   Leino and Moskal (2014), Coinduction Simply, Figure 13.
--
-- EXPECTED: ACCEPT (INDEXED COINDUCTIVE PROOF).
--
-- Proves trivialK xs k for all k by induction on k, then lifts to trivial xs
-- via trivialLemma.
--------------------------------------------------------------------------------

{-@ lazy trivial @-}
{-@ reflect trivial @-}
{-@ trivial :: IStream a -> Bool @-}
trivial :: Stream a -> Bool
trivial (_ :> xs) = trivial xs

{-@ reflect trivialK @-}
{-@ trivialK :: IStream a -> k:Nat -> Bool / [k] @-}
trivialK :: Stream a -> Int -> Bool
trivialK _ 0 = True
trivialK (_ :> xs) k = trivialK xs (k - 1)

{-@
trivialAllK
        :: xs:IStream a
        -> k:Nat
        -> {trivialK xs k}
        / [k]
@-}
trivialAllK :: Stream a -> Int -> Proof
trivialAllK _ 0 = ()
trivialAllK (_ :> xs) k =
  trivialAllK xs (k - 1)

{-@
assume trivialLemma
        :: xs:IStream a
        -> (k:Nat -> {trivialK xs k})
        -> {trivial xs}
@-}
trivialLemma :: Stream a -> (Int -> Proof) -> Proof
trivialLemma _ _ = ()

{-@
trivialAll
        :: xs:IStream a
        -> {trivial xs}
@-}
trivialAll :: Stream a -> Proof
trivialAll xs =
  trivialLemma xs (trivialAllK xs)

--------------------------------------------------------------------------------
-- 6. Merging a stream with itself produces adjacent duplicates
--
-- Sources:
--   Mastorou, Papaspyrou, and Vazou (2022), Coinduction Inductively.
--
-- EXPECTED: ACCEPT (INDEXED COINDUCTIVE PROOF).
--
-- Proves dupK (merge xs xs) k for all k by induction on k, then lifts to
-- dup (merge xs xs) via dupLemma.
--------------------------------------------------------------------------------

{-@ lazy dup @-}
{-@ reflect dup @-}
{-@ dup :: Eq a => IStream a -> Bool @-}
dup :: Eq a => Stream a -> Bool
dup (x1 :> (x2 :> xs)) =
    x1 == x2 && dup xs

{-@ reflect dupK @-}
{-@ dupK :: Eq a => IStream a -> k:Nat -> Bool / [k] @-}
dupK :: Eq a => Stream a -> Int -> Bool
dupK _ 0 = True
dupK (x1 :> (x2 :> xs)) k =
    x1 == x2 && dupK xs (k - 1)

{-@
mergeSelfDupStep
        :: Eq a
        => xs:IStream a
        -> k:{Nat | k > 0}
        -> {dupK (merge xs xs) k
                == dupK (merge (stail xs) (stail xs)) (k - 1)}
@-}
mergeSelfDupStep :: Eq a => Stream a -> Int -> Proof
mergeSelfDupStep s@(x :> xs) k
  =   dupK (merge s s) k
  === dupK (x :> merge s xs) k
  === dupK (x :> (x :> merge xs xs)) k
  === (x == x && dupK (merge xs xs) (k - 1))
  === dupK (merge xs xs) (k - 1)
  === dupK (merge (stail s) (stail s)) (k - 1)
  *** QED

{-@
mergeSelfDupK
        :: Eq a
        => xs:IStream a
        -> k:Nat
        -> {dupK (merge xs xs) k}
        / [k]
@-}
mergeSelfDupK :: Eq a => Stream a -> Int -> Proof
mergeSelfDupK _ 0 = ()
mergeSelfDupK xs@(_ :> _) k =
  mergeSelfDupStep xs k
    ? mergeSelfDupK (stail xs) (k - 1)

{-@
assume dupLemma
        :: Eq a
        => xs:IStream a
        -> (k:Nat -> {dupK xs k})
        -> {dup xs}
@-}
dupLemma :: Eq a => Stream a -> (Int -> Proof) -> Proof
dupLemma _ _ = ()

{-@
mergeSelfDup
        :: Eq a
        => xs:IStream a
        -> {dup (merge xs xs)}
@-}
mergeSelfDup :: Eq a => Stream a -> Proof
mergeSelfDup xs =
  dupLemma
    (merge xs xs)
    (mergeSelfDupK xs)

--------------------------------------------------------------------------------
-- 7. Pointwise multiplication of a stream by itself is non-negative
--
-- Sources:
--   Mastorou, Papaspyrou, and Vazou (2022), Coinduction Inductively.
--
-- EXPECTED: ACCEPT (INDEXED COINDUCTIVE PROOF).
--
-- Proves nnegK (mult xs xs) k for all k by induction on k using squareBounds,
-- then lifts to nneg (mult xs xs) via nnegLemma.
--------------------------------------------------------------------------------

{-@ lazy mult @-}
{-@ reflect mult @-}
{-@ mult :: Num a => IStream a -> IStream a -> IStream a @-}
mult :: Num a => Stream a -> Stream a -> Stream a
mult (x :> xs) (y :> ys) =
  (x * y) :> mult xs ys

{-@ lazy nneg @-}
{-@ reflect nneg @-}
{-@ nneg :: IStream Integer -> Bool @-}
nneg :: Stream Integer -> Bool
nneg (x :> xs) =
  x >= 0 && nneg xs

{-@ reflect nnegK @-}
{-@ nnegK :: IStream Integer -> k:Nat -> Bool / [k] @-}
nnegK :: Stream Integer -> Int -> Bool
nnegK _ 0 = True
nnegK (x :> xs) k =
  x >= 0 && nnegK xs (k - 1)

{-@
squareBounds
        :: x:Integer
        -> {0 <= x * x && x <= x * x}
@-}
squareBounds :: Integer -> Proof
squareBounds x
  | x <= 0    = ()
  | otherwise = ()

{-@
squareNNegK
        :: xs:IStream Integer
        -> k:Nat
        -> {nnegK (mult xs xs) k}
        / [k]
@-}
squareNNegK :: Stream Integer -> Int -> Proof
squareNNegK _ 0 = ()
squareNNegK (x :> xs) k =
  squareBounds x
    ? squareNNegK xs (k - 1)

{-@
assume nnegLemma
        :: xs:IStream Integer
        -> (k:Nat -> {nnegK xs k})
        -> {nneg xs}
@-}
nnegLemma :: Stream Integer -> (Int -> Proof) -> Proof
nnegLemma _ _ = ()

{-@
squareNNeg
        :: xs:IStream Integer
        -> {nneg (mult xs xs)}
@-}
squareNNeg :: Stream Integer -> Proof
squareNNeg xs =
  nnegLemma
    (mult xs xs)
    (squareNNegK xs)

--------------------------------------------------------------------------------
-- 8. Every integer stream is lexicographically below its pointwise square
--
-- Sources:
--   Mastorou, Papaspyrou, and Vazou (2022), Coinduction Inductively.
--   Leino and Moskal (2014), Coinduction Simply, Figure 0.
--
-- EXPECTED: ACCEPT (INDEXED COINDUCTIVE PROOF).
--
-- Proves belowK xs (mult xs xs) k for all k by induction on k using
-- squareBounds, then lifts to below xs (mult xs xs) via belowLemma.
--------------------------------------------------------------------------------

{-@ reflect implies @-}
implies :: Bool -> Bool -> Bool
implies p q = not p || q

{-@ lazy below @-}
{-@ reflect below @-}
{-@ below :: Ord a => IStream a -> IStream a -> Bool @-}
below :: Ord a => Stream a -> Stream a -> Bool
below (x :> xs) (y :> ys) =
  x <= y && implies (x == y) (below xs ys)

{-@ reflect belowK @-}
{-@ belowK :: Ord a => IStream a -> IStream a -> k:Nat -> Bool / [k] @-}
belowK :: Ord a => Stream a -> Stream a -> Int -> Bool
belowK _ _ 0 = True
belowK (x :> xs) (y :> ys) k =
  x <= y && implies (x == y) (belowK xs ys (k - 1))

{-@
belowSquareK
        :: xs:IStream Integer
        -> k:Nat
        -> {belowK xs (mult xs xs) k}
        / [k]
@-}
belowSquareK :: Stream Integer -> Int -> Proof
belowSquareK _ 0 = ()
belowSquareK (x :> xs) k =
  squareBounds x
    ? belowSquareK xs (k - 1)

{-@
assume belowLemma
        :: Ord a
        => xs:IStream a
        -> ys:IStream a
        -> (k:Nat -> {belowK xs ys k})
        -> {below xs ys}
@-}
belowLemma :: Ord a => Stream a -> Stream a -> (Int -> Proof) -> Proof
belowLemma _ _ _ = ()

{-@
belowSquare
        :: xs:IStream Integer
        -> {below xs (mult xs xs)}
@-}
belowSquare :: Stream Integer -> Proof
belowSquare xs =
  belowLemma
    xs
    (mult xs xs)
    (belowSquareK xs)

--------------------------------------------------------------------------------
-- 9. Mapping preserves infinitude on lists
--
-- Sources:
--   Mastorou, Papaspyrou, and Vazou (2022), Coinduction Inductively.
--
-- EXPECTED: ACCEPT (INDEXED COINDUCTIVE PROOF).
--
-- Proves infiniteK (map f xs) k for all k given infinite xs, then lifts to
-- infinite (map f xs) via infLemma.
--------------------------------------------------------------------------------

data L a
  = Nil
  | a :| L a

infixr 5 :|

{-@ lazy infinite @-}
{-@ reflect infinite @-}
infinite :: L a -> Bool
infinite Nil = False
infinite (_ :| xs) = infinite xs

{-@ lazy map @-}
{-@ reflect map @-}
map :: (a -> b) -> L a -> L b
map _ Nil = Nil
map f (x :| xs) = f x :| map f xs

{-@ reflect infiniteK @-}
{-@ infiniteK :: L a -> k:Nat -> Bool / [k] @-}
infiniteK :: L a -> Int -> Bool
infiniteK _ 0 = True
infiniteK Nil _ = False
infiniteK (_ :| xs) k =
  infiniteK xs (k - 1)

{-@
infiniteToK
        :: xs:L a
        -> k:Nat
        -> {v:Proof | infinite xs}
        -> {infiniteK xs k}
        / [k]
@-}
infiniteToK :: L a -> Int -> Proof -> Proof
infiniteToK _ 0 _ = ()
infiniteToK Nil _ _ = ()
infiniteToK (_ :| xs) k _ =
  infiniteToK xs (k - 1) ()

{-@
mapInfiniteK
        :: f:(a -> b)
        -> xs:L a
        -> k:Nat
        -> {v:Proof | infiniteK xs k}
        -> {infiniteK (map f xs) k}
        / [k]
@-}
mapInfiniteK :: (a -> b) -> L a -> Int -> Proof -> Proof
mapInfiniteK _ _ 0 _ = ()
mapInfiniteK _ Nil _ _ = ()
mapInfiniteK f (_ :| xs) k _ =
  mapInfiniteK f xs (k - 1) ()

{-@
assume infLemma
        :: xs:L a
        -> (k:Nat -> {infiniteK xs k})
        -> {infinite xs}
@-}
infLemma :: L a -> (Int -> Proof) -> Proof
infLemma _ _ = ()

{-@
mapInfinite
        :: f:(a -> b)
        -> xs:{L a | infinite xs}
        -> {infinite (map f xs)}
@-}
mapInfinite :: (a -> b) -> L a -> Proof
mapInfinite f xs =
  infLemma
    (map f xs)
    (\k ->
      mapInfiniteK
        f
        xs
        k
        (infiniteToK xs k ()))

--------------------------------------------------------------------------------
-- 10. Map fusion on potentially infinite lists
--
-- Sources:
--   Mastorou, Papaspyrou, and Vazou (2022), Coinduction Inductively.
--
-- EXPECTED: ACCEPT (INDEXED COINDUCTIVE PROOF).
--
-- Proves eqKList (map f (map g xs)) (map (compose f g) xs) k by induction on
-- k, then lifts to list equality via approxL.
--------------------------------------------------------------------------------

{-@ reflect takeL @-}
{-@ takeL :: k:Nat -> L a -> [a] / [k] @-}
takeL :: Int -> L a -> [a]
takeL 0 _ = []
takeL _ Nil = []
takeL k (x :| xs) =
  x : takeL (k - 1) xs

{-@ reflect eqKList @-}
{-@ eqKList :: Eq a => L a -> L a -> k:Nat -> Bool / [k] @-}
eqKList :: Eq a => L a -> L a -> Int -> Bool
eqKList _ _ 0 = True
eqKList Nil Nil _ = True
eqKList (x :| xs) (y :| ys) k =
  x == y && eqKList xs ys (k - 1)
eqKList _ _ _ = False

{-@ reflect lcons @-}
lcons :: a -> L a -> L a
lcons x xs = x :| xs

{-@
eqConsL
        :: Eq a
        => x:a
        -> xs:L a
        -> k:{Nat | k > 0}
        -> y:a
        -> ys:L a
        -> {v:Proof | x == y}
        -> {v:Proof | eqKList xs ys (k - 1)}
        -> {eqKList (lcons x xs) (lcons y ys) k}
@-}
eqConsL
  :: Eq a
  => a
  -> L a
  -> Int
  -> a
  -> L a
  -> Proof
  -> Proof
  -> Proof
eqConsL _ _ _ _ _ _ _ = ()

{-@
eqKLemmaL
        :: Eq a
        => xs:L a
        -> ys:L a
        -> k:Nat
        -> {eqKList xs ys k <=> takeL k xs == takeL k ys}
        / [k]
@-}
eqKLemmaL :: Eq a => L a -> L a -> Int -> Proof
eqKLemmaL _ _ 0 = ()
eqKLemmaL Nil Nil _ = ()
eqKLemmaL (_ :| xs) (_ :| ys) k =
  eqKLemmaL xs ys (k - 1)
eqKLemmaL _ _ _ = ()

{-@
assume takeLemmaL
        :: xs:L a
        -> ys:L a
        -> (k:Nat -> {takeL k xs == takeL k ys})
        -> {xs == ys}
@-}
takeLemmaL :: L a -> L a -> (Int -> Proof) -> Proof
takeLemmaL _ _ _ = ()

{-@
approxL
        :: Eq a
        => xs:L a
        -> ys:L a
        -> (k:Nat -> {eqKList xs ys k})
        -> {xs == ys}
@-}
approxL :: Eq a => L a -> L a -> (Int -> Proof) -> Proof
approxL xs ys p =
  takeLemmaL xs ys (\k -> eqKLemmaL xs ys k ? p k)

{-@
mapFusionListK
        :: Eq c
        => f:(b -> c)
        -> g:(a -> b)
        -> xs:L a
        -> k:Nat
        -> {eqKList (map f (map g xs)) (map (compose f g) xs) k}
        / [k]
@-}
mapFusionListK
  :: Eq c
  => (b -> c)
  -> (a -> b)
  -> L a
  -> Int
  -> Proof
mapFusionListK _ _ _ 0 = ()
mapFusionListK _ _ Nil _ = ()
mapFusionListK f g (x :| xs) k =
  eqConsL
    (f (g x))
    (map f (map g xs))
    k
    ((compose f g) x)
    (map (compose f g) xs)
    ()
    (mapFusionListK f g xs (k - 1))

{-@
mapFusionList
        :: Eq c
        => f:(b -> c)
        -> g:(a -> b)
        -> xs:L a
        -> {map f (map g xs) == map (compose f g) xs}
@-}
mapFusionList
  :: Eq c
  => (b -> c)
  -> (a -> b)
  -> L a
  -> Proof
mapFusionList f g xs =
  approxL
    (map f (map g xs))
    (map (compose f g) xs)
    (mapFusionListK f g xs)
