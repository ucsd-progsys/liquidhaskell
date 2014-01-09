module Fixme where

import Prelude hiding (repeat, take, head)
import Language.Haskell.Liquid.Prelude


{-@ LIQUID "--no-termination" @-}

{-@ measure inf :: [a] -> Prop 
    inf([])   = false
    inf(x:xs) = (inf xs)
  @-}


-- or any pred *implied* by (inf v)
{-@ repeat :: a -> {v:[a] | (inf v)} @-}
repeat :: a -> [a]
repeat x = x : repeat x

{-@ repeat' :: l:Int -> a -> {v:[a] | (len v) = l} @-}
repeat' :: Int -> a -> [a]
repeat' k x = x : repeat' (k-1) x


{-@ take :: xs:[a] -> {v:Nat|((inf xs) || (v < (len xs))) } -> [a] @-}
take :: [a] -> Int -> [a]
take [] _ = liquidError "take"
take _ 0 = []
take (x:xs) i = x : take xs (i-1)


{-@ head :: {v:[a] | (((len v) > 0) || (inf v)) } -> a @-}
head :: [a] -> a
head (x:_) = x
head _     = liquidError "head"



good1 = let x = head (repeat 0) in liquidAssert (x == 0)
good2 = let x = head ([0, 1]) in liquidAssert (True) -- x == 0
bad1  = let x = head (repeat 0) in liquidAssert (x == 12)
bad2  = let x = head [] in liquidAssert (x == 12)


foo = take (repeat 0) 5

-- bar = (\x -> liquidAssert (False)) (repeat 0)



