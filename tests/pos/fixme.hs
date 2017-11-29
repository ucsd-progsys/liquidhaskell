{-# LANGUAGE GADTs #-}

{-@ LIQUID "--no-termination" @-}

{-@ data List a where
       Nil  :: List a
     | Cons :: poopy:a -> listTail:List a -> List a
  @-}

data List a where
  Nil  :: List a
  Cons :: a -> List a -> List a

test :: List a -> Int
test Nil = 1
test (Cons x xs) = 1 + test xs
