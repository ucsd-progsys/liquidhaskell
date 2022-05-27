{-@ LIQUID "--pruneunsorted" @-}

-- | A somewhat fancier example demonstrating the use of Abstract Predicates and exist-types

module Ex1 (llen) where

-------------------------------------------------------------------------
-- | Data types ---------------------------------------------------------
-------------------------------------------------------------------------

data Vec a = Nil | Cons a (Vec a)

{-@ data Vec [llen] a = Nil | Cons { vx::a, vxs :: Vec a } @-}

-- | We can encode the notion of length as an inductive measure @llen@

{-@ measure llen @-}
llen :: Vec a -> Int
llen (Nil)       = 0
llen (Cons x xs) = 1 + llen xs


-- | As a warmup, lets check that a /real/ length function indeed computes
-- the length of the list.

{-@ sizeOf :: xs:Vec a -> {v: Int | v = llen xs} @-}
sizeOf             :: Vec a -> Int
sizeOf Nil         = 0
sizeOf (Cons _ xs) = 1 + sizeOf xs

-------------------------------------------------------------------------
-- | Higher-order fold --------------------------------------------------
-------------------------------------------------------------------------

-- | Time to roll up the sleeves. Here's a a higher-order @foldr@ function
-- for our `Vec` type. Note that the `op` argument takes an extra /ghost/
-- parameter that will let us properly describe the type of `efoldr`

{-@ efoldr :: forall a b <p :: x0:Vec a -> x1:b -> Bool>.
                (xs:Vec a -> x:a -> b <p xs> -> b <p (Ex1.Cons x xs)>)
              -> b <p Ex1.Nil>
              -> ys: Vec a
              -> b <p ys>
  @-}
efoldr :: (Vec a -> a -> b -> b) -> b -> Vec a -> b
efoldr op b Nil         = b
efoldr op b (Cons x xs) = op xs x (efoldr op b xs)

-------------------------------------------------------------------------
-- | Clients of `efold` -------------------------------------------------
-------------------------------------------------------------------------

-- | Finally, lets write a few /client/ functions that use `efoldr` to
-- operate on the `Vec`s.

-- | First: Computing the length using `efoldr`
{-@ size :: xs:Vec a -> {v: Int | v = llen xs} @-}
size :: Vec a -> Int
size = efoldr (\_ _ n -> n + 1) 0

-- | Second: Appending two lists using `efoldr`
{-@ app  :: xs: Vec Int -> ys: Vec Int -> {v: Vec Int | llen v = llen xs + llen ys } @-}
app :: Vec Int -> Vec Int -> Vec Int
app xs ys = efoldr (\_ z zs -> Cons z zs) ys xs
