
{-@ LIQUID "--exact-data-con"                      @-}
{- LIQUID "--higherorder"                         @-}
{- LIQUID "--totality"                            @-}
{- LIQUID "--automatic-instances=liquidinstances" @-}

module ReflectLib3 where

{-@ reflect incr @-}
incr :: Int -> Int
incr x = x + 1

{-@ data Day = Mon | Tue @-}
data Day = Mon | Tue

{-@ reflect next @-}
next :: Day -> Day
next Mon = Tue
next Tue = Mon

-- | Lists ---------------------------------------------------------------------

{-@ data List [llen] a = Nil | Cons {lHd :: a, lTl :: List} @-}
data List a = Nil | Cons a (List a)

{-@ measure llen @-}
{-@ llen :: List a -> Nat @-}
llen :: List a -> Int
llen Nil        = 0
llen (Cons h t) = 1 Prelude.+ llen t

{-@ reflect app @-}
app :: List a -> List a -> List a
app Nil         ys = ys
app (Cons x xs) ys = Cons x (app xs ys)
