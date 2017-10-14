module Fold where

{-@ LIQUID "--no-termination" @-}
import Prelude hiding (foldr)

data Vec a = Nil | Cons a (Vec a)



{-@
efoldl :: forall <inv :: (Vec a) -> b -> Bool, step :: a -> b -> b -> Bool>.
          {y::a, ys :: Vec a, z :: {v:Vec a | v = Cons y ys && llen v = llen ys + 1}, jacc:: b<inv z> |- b<step y jacc> <: b<inv ys>}
         (x:a -> pacc:b -> b<step x pacc>)
      -> xs:(Vec a)
      -> b<inv xs>
      -> b<inv Nil>
@-}

efoldl :: (a -> b -> b) -> Vec a -> b -> b
efoldl op Nil b         = b
efoldl op (Cons x xs) b = efoldl op xs (x `op` b)




{-
step x b b' <=> b' = b + 1
inv ys b <=> b + len ys = len xs
-}

{-@ size_invariant_qualifier :: xs: Vec a -> ys:Vec a -> {v:Int | v + llen xs ==  llen ys} @-}
size_invariant_qualifier :: Vec a -> Vec a -> Int
size_invariant_qualifier xs ys = undefined

{-@ size :: xs:Vec a -> {v: Int | v = llen xs} @-}
size :: Vec a -> Int
size xs = efoldl (\_ n -> n + 1) xs 0


-- | We can encode the notion of length as an inductive measure @llen@

{-@ measure llen @-}

llen :: Vec a -> Int
llen (Nil)       = 0
llen (Cons x xs) = 1 + llen(xs)


-------------------------------------------------------------------------
-- | Clients of `efold` -------------------------------------------------
-------------------------------------------------------------------------


-- | The above uses a helper that counts up the size. (Pesky hack to avoid writing qualifier v = ~A + 1)
{-@ suc :: x:Int -> {v: Int | v = x + 1} @-}
suc :: Int -> Int
suc x = x + 1

{-@ LIQUID "--maxparams=3" @-}
{-@ append_invariant_qualifier :: xs: Vec a -> ys:Vec a -> zs:Vec a -> {v:Vec a | llen v + llen xs ==  llen ys + llen zs } @-}
append_invariant_qualifier :: Vec a -> Vec a -> Vec a -> Vec a
append_invariant_qualifier xs ys zs = undefined

-- | Second: Appending two lists using `efoldl`
{-@ app  :: xs: Vec a -> ys: Vec a -> {v: Vec a | llen v = llen xs + llen ys } @-}
app xs ys = efoldl (\z zs -> Cons z zs) xs ys
