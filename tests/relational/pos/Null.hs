module Fixme where

import           Prelude                 hiding ( null )

data List a = Nil | Cons a (List a)

{-@ null :: l:List Int -> Bool @-}
null :: List Int -> Bool
null Nil = True
null _   = False

{-@ null' :: l:List Int -> Bool @-}
null' :: List Int -> Bool
null' (Cons _ _)   = False
null' Nil = True

{-@ relational null' ~ null :: { l1:List Int -> Bool ~ l2:List Int -> Bool 
                            | l1 == l2 :=> r1 l1 == r2 l2 } @-}
