{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module Lists where

import Prelude hiding (map, rev, sum) -- ((+), (+), Eq (..), Ord (..), Char, Int, Bool (..))
import Language.Haskell.Liquid.ProofCombinators

-- | List Definition -----------------------------------------------------------

{-@ data List [llen] @-} 
data List a = Nil | Cons a (List a)

{-@ measure llen @-}
{-@ llen :: List a -> Nat @-}
llen :: List a -> Int
llen Nil        = 0
llen (Cons h t) = 1 + llen t

-- | Map -----------------------------------------------------------------------

{-@ reflect map @-}
map :: (a -> b) -> List a -> List b
map f Nil         = Nil
map f (Cons x xs) = Cons (f x) (map f xs)

{-@ reflect up @-}
up :: Int -> Int
up x = x + 1

{-@ thmMapIncr :: xs:List Int -> { sum (map up xs) == sum xs + llen xs } @-}
thmMapIncr :: List Int -> Proof
thmMapIncr Nil         =  ()

thmMapIncr (Cons x xs) = [ -- sum (map up (Cons x xs))
                           -- ==. sum (Cons (up x) (map up xs))
                           -- ==. (up x) + sum (map up xs) ?
                           thmMapIncr xs
                           -- ==. (x + 1) + (sum xs + llen xs)
                           -- ==. sum (Cons x xs) + llen (Cons x xs)
                         ] *** QED

{-@ reflect sum @-}
sum :: List Int -> Int
sum Nil         = 0
sum (Cons x xs) = x + sum xs
