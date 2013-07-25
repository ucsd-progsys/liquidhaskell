{--! run liquid with no-termination -}

module SimpleRefinements where
import Prelude hiding ((!!), length)
import Language.Haskell.Liquid.Prelude


-- |Simple Refinement Types

{-@ zero :: {v:Int | v = 0} @-}
zero     :: Int
zero     =  0

{-@ type Even = {v:Int | v mod 2 = 0} @-}

{-@ zero'' :: Even @-}
zero''     :: Int
zero''     =  0

-- |Lists

infixr `C`
data L a = N | C a (L a)

{-@ natList :: L Nat @-}
natList     :: L Int
natList     =  0 `C` 1 `C` 3 `C` N

{-@ evenList :: L Even @-}
evenList     :: L Int
evenList     =  0 `C` 2 `C` 8 `C` N

-- |Dependent Functions

{-@ safeDiv :: Int -> {v:Int | v != 0} -> Int @-}
safeDiv     :: Int -> Int -> Int
safeDiv x y = x `div` y

n = 4 `safeDiv` 2 

{-@ SimpleRefinements.!! :: ls:(L a) -> {v:Nat | v < (llen ls)} -> a @-}
(!!)       :: L a -> Int -> a
(C x _) !!0 = x
(C _ xs)!!n = xs!!(n-1)
_       !!_ = liquidError "This should not happen!"

{-@ measure llen :: (L a) -> Int
    llen(N)      = 0
    llen(C x xs) = 1 + (llen xs)
  @-}

{-@ length :: xs:(L a) -> {v:Int | v = (llen xs)} @-}
length     :: L a -> Int
length N        = 0
length (C _ xs) = 1 + (length xs)

a = (1 `C` 2 `C` 3 `C` 4 `C` N) !! 3

-- | Checking index
loop :: Int -> Int -> a -> (Int -> a -> a) -> a
loop lo hi base f = go lo base
  where go i acc | i < hi    = go (i+1) (f i acc)
                 | otherwise = acc

{-@ listNatSum :: L Nat -> Nat @-}
listNatSum     :: L Int -> Int
listNatSum xs  = loop 0 n 0 body 
  where body   = \i acc -> acc + (xs !! i)
        n      = length xs

{-@ listEvenSum :: L Even -> Even @-}
listEvenSum     :: L Int -> Int
listEvenSum xs  = loop 0 n 0 body 
  where body   = \i acc -> acc + (xs !! i)
        n      = length xs
