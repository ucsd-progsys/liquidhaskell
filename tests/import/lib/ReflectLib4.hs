{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module ReflectLib4 where

-- | Lists ---------------------------------------------------------------------

{-@ data List [llen] @-} -- a = Nil | Cons {lHd :: a, lTl :: List a} @-}
data List a = Nil | Cons {lHd :: a, lTl :: List a} 

{-@ measure llen @-}
{-@ llen :: List a -> Nat @-}
llen :: List a -> Int
llen Nil        = 0
llen (Cons h t) = 1 + llen t

-- TODO: make this work WITHOUT the invariant
{-@ invariant {v:List a | 0 <= llen v} @-}

{-@ reflect app @-}
app :: List a -> List a -> List a
app Nil         ys = ys
app (Cons x xs) ys = Cons x (app xs ys)

{-@ reflect gapp @-}
gapp :: List a -> List a
gapp Nil         = Nil
gapp (Cons x xs) = Nil

{-@ test4 :: { gapp Nil = Nil } @-}
test4 = ()
