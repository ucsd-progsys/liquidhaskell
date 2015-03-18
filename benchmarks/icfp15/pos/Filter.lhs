\begin{code}
module OverView where 

import Prelude hiding ((.), filter)
import Language.Haskell.Liquid.Prelude

{-@ LIQUID "--no-termination" @-}
\end{code}

\begin{code}
witness :: Eq a => (a -> Bool) -> (a -> Bool -> Bool) -> a -> Bool -> a -> Bool
witness p w = \ y b v -> b ==> w y b ==> (v == y) ==> p v 

{-@ bound witness @-}
{-@ filter :: forall <p :: a -> Prop, w :: a -> Bool -> Prop>.
                  (Witness a p w) => 
                  (x:a -> Bool<w x>) -> [a] -> [a<p>]
  @-}

filter :: (a -> Bool) -> [a] -> [a]
filter f (x:xs)
  | f x       = x : filter f xs
  | otherwise = filter f xs
filter _ []   = []


{-@ measure isPrime :: Int -> Prop @-}
isPrime :: Int -> Bool 
{-@ isPrime :: n:Int -> {v:Bool | Prop v <=> isPrime n} @-}
isPrime = undefined

-- | `positives` works by instantiating:
-- p := \v   -> isPrime v
-- q := \n v -> Prop v <=> isPrime n

	
{-@ primes :: [Int] -> [{v:Int | isPrime v}] @-}
primes     = filter isPrime
\end{code}