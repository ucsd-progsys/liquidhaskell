{-# LANGUAGE GADTs #-}

{-@ LIQUID "--no-termination" @-}

{-@ data List a where
    Nil  :: List a 
  | Cons :: listHead:a -> listTail:List a -> List a  
@-}

{-@ data List1 a b where
    Nil1  :: List1 a b  
  | Cons1 :: listHead:a -> listTail:List a -> List1 a b
@-}

{-@ data List2 a b <p :: a -> Prop> where
    Nil2  :: List2 a 
  | Cons2 :: listHead:a -> listTail:List a -> List2 a b
@-}


data List a where
  Nil  :: List a
  Cons :: a -> List a -> List a


data List1 a b where
  Nil1  :: List1 a b
  Cons1 :: a -> List a -> List1 a b

data List2 a b where
  Nil2  :: List2 a b
  Cons2 :: a -> List a -> List2 a b


test :: List a -> Int 
test Nil = 1 
test (Cons x xs) = 1 + test xs 