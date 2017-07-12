\begin{code}
module OverView where

import Prelude hiding ((.), filter)
import Language.Haskell.Liquid.Prelude

{-@ LIQUID "--no-termination" @-}
\end{code}

\begin{code}
{-@ filter :: forall <p :: a -> Bool, w :: a -> Bool -> Bool>.
                  {y :: a, b::{v:Bool<w y> | v}|- {v:a| v == y} <: a<p>}
                  (x:a -> Bool<w x>) -> [a] -> [a<p>]
  @-}

filter :: (a -> Bool) -> [a] -> [a]
filter f (x:xs)
  | f x       = x : filter f xs
  | otherwise = filter f xs
filter _ []   = []


{-@ measure isPrime :: Int -> Bool @-}
isPrimeP :: Int -> Bool
{-@ isPrimeP :: n:Int -> {v:Bool | v <=> isPrime n} @-}
isPrimeP = undefined

-- | `positives` works by instantiating:
-- p := \v   -> isPrime v
-- q := \n v -> Bool v <=> isPrime n


{-@ primes :: [Int] -> [{v:Int | isPrime v}] @-}
primes     = filter isPrimeP
\end{code}
