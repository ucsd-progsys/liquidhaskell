module SList where

infixr `C`

data L a = N | C a (L a)

{-@
data L a <p :: a -> a -> Prop>
  = N 
  | C (h :: a) (tl :: (L <p> a<p h>))
@-}

{-@ type SL a = L <{\hd v -> v >= hd}> a @-}


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
