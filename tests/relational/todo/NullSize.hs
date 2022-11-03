module Fixme where

import           Prelude                 hiding ( null )

data List a = Nil | Cons a (List a)

{-@ measure size @-}
{-@ size :: l:List Int -> {v:Nat | ((v == 0) <=> (is$Fixme.Nil l))} @-}
size :: List Int -> Int
size Nil         = 0
size (Cons _ xs) = 1 + size xs

{-@ measure null @-}
null :: List Int -> Bool
null Nil = True
null _   = False

-- {-@ thm :: l1:List Int -> l2:List Int -> 
--             { v:() | Fixme.size l1 == Fixme.size l2 } -> {Fixme.null l1 <=> Fixme.null l2} @-}
-- thm :: List Int -> List Int -> () -> ()
-- thm l1 l2 () = ()

{-@ relational null ~ null :: {l1:List Int -> Bool 
                            ~ l2:List Int -> Bool 
                           | (Fixme.size l1 == Fixme.size l2) :=> ((r1 l1) <=> (r2 l2))} @-}
