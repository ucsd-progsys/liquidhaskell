module Fixme where

import           Prelude                 hiding ( null )

data List a = Nil | Cons a (List a)

{-@ null :: l:List a -> {v:Bool|v <=> l == Nil} @-}
null :: List a -> Bool
null Nil = True
null _   = False

nullInt, nullBool :: Bool
nullInt = null (Cons () Nil)
nullBool = null (Cons True Nil)

{-@ relational nullInt ~ nullBool :: _ ~ _ ~~ r1 == r2 @-}
