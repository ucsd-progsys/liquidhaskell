-- | With ADTs, the below fails with a nasty 'elaborate' error, when
--   the actual problem is a malformed refined data-declaration where
--   the type variable 'a' has been left out.
--
--   We should flag a proper malformed data-declaration error instead.

{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module BadDataDecl where

{-@ data L = Emp | Bons {x::a, zonk :: a, xs:: (L a)} @-}
--       ^ whoops, missing a tyvar!

data L a = Emp | Cons a (L a)

{-@ reflect sz @-}
sz :: L a -> Int
sz Emp         = 0
sz (Cons _ xs) = 1 + sz xs

{-@ test :: {(sz (Cons 1 Emp)) = 1} @-}
test :: ()
test = ()
