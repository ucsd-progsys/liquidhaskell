module Termination (fac, tailFac, map) where

import Prelude hiding (gcd, mod, map, repeat, take)
import Language.Haskell.Liquid.Prelude

map   :: (a -> b) -> List a -> List b
merge :: (Ord a) => List a -> List a -> List a


-------------------------------------------------------------------------
-- | Simple Termination
-------------------------------------------------------------------------

fac   :: Int -> Int
fac 0 = 1
fac 1 = 1
fac n = n * fac (n-1)




-------------------------------------------------------------------------
-- | Semantic Termination
-------------------------------------------------------------------------

gcd :: Int -> Int -> Int
gcd a 0 = a
gcd a b = gcd b (a `mod` b)


mod :: Int -> Int -> Int
mod a b
  | a - b >  b = mod (a - b) b
  | a - b <  b = a - b
  | a - b == b = 0

-------------------------------------------------------------------------
-- Explicit Metrics #1 
-------------------------------------------------------------------------

tailFac   :: Int -> Int
tailFac n = loop 1 n

loop      :: Int -> Int -> Int
loop      = undefined

         


-------------------------------------------------------------------------
-- Explicit Metrics #2 
-------------------------------------------------------------------------

range :: Int -> Int -> [Int]
range lo hi = undefined



-------------------------------------------------------------------------
-- | Structural Recursion 
-------------------------------------------------------------------------

data List a = N | C a (List a)

{-@ map :: (a -> b) -> xs:List a -> List b @-}
map _ N        = N
map f (C x xs) = map f (C x xs) -- f x `C` map f xs


{-@ measure size @-}
size          :: List a -> Int 
size (N)      = 0
size (C x xs) = 1 + size xs


-------------------------------------------------------------------------
-- | Default Metrics
-------------------------------------------------------------------------

-- data List ...


map' _ N        = N
map' f (C x xs) = f x `C` map' f xs



-------------------------------------------------------------------------
-- | Termination Expressions Metrics
-------------------------------------------------------------------------

{- merge :: xs:_ -> ys:_ -> _ / [sz xs + sz ys] -}

merge (C x xs) (C y ys)
  | x < y      = x `C` merge xs (y `C` ys)
  | otherwise  = y `C` merge (x `C` xs) ys
merge _   ys   = ys









-------------------------------------------------------------------------
-- | Infinite Streams
-------------------------------------------------------------------------

{- data List [sz] a <p :: List a -> Prop>
      = N | C { x  :: a
              , xs :: List <p> a <<p>>
              }
  -}


{-@ measure emp  :: (List a) -> Prop
    emp (N)      = true
    emp (C x xs) = false
  @-}

{- type Stream a = {xs: List <{\v -> not (emp v)}> a | not (emp xs)} @-}

{- Lazy repeat @-}
                 
{- repeat :: a -> Stream a @-}
-- repeat   :: a -> List a
-- repeat x = x `C` repeat x


{- take :: Nat -> Stream a -> List a @-}
-- take  :: Int -> List a -> List a
-- take 0 _        = N
-- take n (C x xs) = x `C` take (n-1) xs
-- take _ N        = liquidError "never happens"



























-----------------------------------------------------


{- invariant {v : List a | 0 <= size v} -}








