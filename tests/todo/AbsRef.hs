module AbsRef where

data F a = F a
{-@ data F a <p :: a -> Prop> = F (x :: a)@-}



{-@ foo :: F <{\v -> true}, {\v -> true}> Int @-}
foo :: F Int
foo = F 5