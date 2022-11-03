{-@ LIQUID "--expect-any-error" @-}
module Fixme where

import           Prelude                 hiding ( null )

data List a = Nil | Cons a (List a)

{-@ measure size @-}
{-@ size :: l:List a -> {v:Nat | ((v == 0) <=> (is$Fixme.Nil l)) } @-}
size :: List a -> Int
size Nil         = 0
size (Cons _ xs) = 1 + size xs

{-@ null :: l:List a -> Bool @-}
null :: List a -> Bool
null Nil = True
null _   = False

{-@ relational null ~ null :: {l1:List a -> Bool 
                            ~ l2:List b -> Bool 
                           | true ==> r1 l1 == r2 l2} @-}
