{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module ReflectLib5 where

-- | Days ---------------------------------------------------------------------

{-@ data Day = Mon | Tue @-}
data Day = Mon | Tue

{-@ reflect next @-}
next :: Day -> Day
next Mon = Tue
next Tue = Mon

{-@ reflect lDay @-}
lDay :: List a -> Day
lDay Nil      = Mon
lDay (Cons x) = Tue

-- | Lists ---------------------------------------------------------------------

data List  a = Nil | Cons {lHd :: a}

{-@ reflect gapp @-}
gapp :: List a -> List a
gapp Nil      = Nil
gapp (Cons x) = Cons x

{-@ test4 :: { gapp Nil = Nil } @-}
test4 = ()
