module Fixme where

import           Prelude                 hiding ( null )

data List a = Nil | Cons a (List a)

{-@ measure size @-}
{-@ size :: List a -> Nat @-}
size :: List a -> Int
size Nil = 0
size (Cons _ xs) = 1 + size xs

{-@ null :: l:List Int -> {v:Bool| v <=> (size l == 0)} @-}
null :: List Int -> Bool
null Nil = True
null _   = False

{-@ relational null ~ null :: l1:List Int -> Bool ~ l2:List Int -> Bool 
                           ~~ (Fixme.size l1 == Fixme.size l2) => ((r1 l1) <=> (r2 l2)) @-}
