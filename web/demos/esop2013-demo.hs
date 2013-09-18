module SList where

infixr `C`

data L a = N
         | C a (L a)

{-@
data L [llen] a <p :: a -> a -> Prop>
  = N 
  | C (h :: a) (tl :: (L <p> a<p h>))
@-}

{-@ type SL a = L <{\hd v -> v >= hd}> a @-}

{-@ invariant {v:L a | (llen v) >= 0} @-}

{-@ measure llen :: (L a) -> Int
    llen(N)      = 0
    llen(C x xs) = 1 + (llen xs)
  @-}

{-@ slist :: SL Int @-}
slist :: L Int
slist = 1 `C` 6 `C` 12 `C` N

{-@ insert :: (Ord a) => a -> SL a -> SL a @-}
insert :: (Ord a) => a -> L a -> L a
insert y N                      = y `C` N                           
insert y (x `C` xs) | y <= x    = y `C` x `C` xs
                    | otherwise = x `C` insert y xs


{-@ insertSort :: (Ord a) => [a] -> SL a@-}
insertSort :: (Ord a) => [a] -> L a
insertSort = foldr insert N
