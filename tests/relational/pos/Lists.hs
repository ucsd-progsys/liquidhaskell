
--
-- Liquidate your assets: reasoning about resource usage in Liquid Haskell.
--

{-@ LIQUID "--reflection" @-}

module Lists (module Lists) where

import Prelude hiding
  ( Functor(..)
  , Applicative(..)
  , Monad(..)
  , drop
  , length
  , take
  )

import RTick
import Language.Haskell.Liquid.ProofCombinators
import Erasure

{-@ type OList a = [a]<{\h x -> h <= x }> @-}

--
-- Some functions on lists. Throughout this file the cost model is the number
-- of recursive calls.
--

-------------------------------------------------------------------------------
-- | Measures:
-------------------------------------------------------------------------------

{-@ measure length @-}
{-@ length :: [a] -> Nat @-}
length :: [a] -> Int
length []       = 0
length (_ : xs) = 1 + length xs

-------------------------------------------------------------------------------
-- | Functions:
-------------------------------------------------------------------------------

--
-- Constructing lists:
--

--
-- We redefine ':' because Liquid Haskell doesn't like @(x:)@ in some
-- proofs.
--
{-@ reflect cons @-}
{-@ cons :: forall <p :: a -> a -> Bool>. x:a -> xs:[a<p x>]<p>
     -> { zs:[a]<p> |  1 + length xs == length zs }
@-}
cons :: a -> [a] -> [a]
cons x xs = x : xs

--
-- Taking and dropping:
--

{-@ reflect takeLE @-}
{-@ takeLE :: n:Nat -> { xs:[a] | n <= length xs }
     -> { t:Tick { zs:[a] | n == length zs } | tcost t == n }
@-}
takeLE :: Int -> [a] -> Tick [a]
takeLE _ []       = pure []
takeLE 0 _        = pure []
takeLE n (x : xs) = pure (cons x) </> takeLE (n - 1) xs

{-@ reflect dropLE @-}
{-@ dropLE :: n:Nat -> { xs:[a] | n <= length xs }
     -> { t:Tick { zs:[a] | length xs - n  == length zs } | tcost t == n }
@-}
dropLE :: Int -> [a] -> Tick [a]
dropLE _ []       = pure []
dropLE 0 xs       = pure xs
dropLE n (_ : xs) = step 1 (dropLE (n - 1) xs)

-------------------------------------------------------------------------------
-- | Erasure proofs:
-------------------------------------------------------------------------------
--
-- We prove that erasing the annotations from 'takeLE' and 'dropLE'
-- returns the standard 'take' and 'drop' functions.
--

-- Functions: -----------------------------------------------------------------

{-@ reflect take @-}
{-@ take :: n:Nat -> { xs:[a] | n <= length xs } -> {o:[a] | length o == n } @-}
take :: Int -> [a] -> [a]
take _ []       = []
take 0 _       = []
take n (x : xs) = x : take (n - 1) xs

{-@ reflect drop @-}
{-@ drop :: n:Nat -> { xs:[a] | n <= length xs } -> {o:[a] | length o == length xs - n }@-}
drop :: Int -> [a] -> [a]
drop _ []       = []
drop 0 xs       = xs
drop n (_ : xs) = drop (n - 1) xs

-- Proofs: --------------------------------------------------------------------

{-@ takeLE_erase :: n:Nat -> { xs:[a] | n <= length xs }
     -> { erase (takeLE n xs) == take n xs }
@-}
takeLE_erase :: Int -> [a] -> Proof
takeLE_erase n []
  =   erase (takeLE n [])
   -- { defn. of takeLE }
  === erase (pure [])
   ? erase_pure []
  === []
   -- { defn. of take }
  === take n []
  *** QED
takeLE_erase 0 xs
  =   erase (takeLE 0 xs)
   -- { defn. of takeLE }
  === erase (pure [])
   ? erase_pure []
  === []
   -- { defn. of take }
  === take 0 xs
  *** QED
takeLE_erase n (x : xs)
  =   erase (takeLE n (x : xs))
   -- { defn. of takeLE }
  === tval (pure (cons x) </> takeLE (n - 1) xs)
   ? takeLE_erase (n - 1) xs
   ? erase_pure (cons x)
   ? erase_wapp (cons x) (take (n - 1) xs) (pure (cons x)) (takeLE (n - 1) xs)
  === cons x (take (n - 1) xs)
   -- { defn. of cons }
  === x : take (n - 1) xs
   -- { defn. of take }
  === take n (x : xs)
  *** QED

{-@ dropLE_erase :: n:Nat -> { xs:[a] | n <= length xs }
     -> { erase (dropLE n xs) == drop n xs }
@-}
dropLE_erase :: Int -> [a] -> Proof
dropLE_erase n []
  =   erase (dropLE n [])
   -- { defn. of dropLE }
  === erase (pure [])
   ? erase_pure []
  === []
   -- { defn. of drop }
  === drop n []
  *** QED
dropLE_erase 0 xs
  =   erase (dropLE 0 xs)
   -- { defn. of dropLE }
  === erase (pure xs)
   ? erase_pure xs
  === xs
   -- { defn. of drop }
  === drop 0 xs
  *** QED
dropLE_erase n (x : xs)
  =   erase (dropLE n (x : xs))
   -- { defn. of dropLE }
  === erase (step 1 (dropLE (n - 1) xs))
   ? dropLE_erase (n - 1) xs
   ? erase_step 1 (drop (n - 1) xs) (dropLE (n - 1) xs)
  === drop n (x : xs)
  *** QED


data P a b = P a b
{-@ data P a b <p :: a -> b -> Bool> = P {left :: a, rigth :: b<p left>}@-}
{-@ reflect split @-}
split :: [a] -> P [a] [a]
{-@ split
     :: x:[a]
     -> P <{\l r -> (2
        <= length x =>
        (length l < length x && length r < length x))
        && length l + length r
        == length x && (((length x) mod 2 == 0 )
        => (length l == length x / 2 && length r
        == length x / 2))}> [a] [a]
@-}

split xs = P (take n xs) (drop n xs)
    where n = length xs `div` 2