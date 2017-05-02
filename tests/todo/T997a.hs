{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--totality"                            @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}
{-@ LIQUID "--diff"                                @-}

module Lists where

import Language.Haskell.Liquid.ProofCombinators


{-@ data List [llen] = Nil | Cons {lHd :: Int, lTl :: List} @-}
data List = Nil | Cons Int List

{-@ measure llen @-}
{-@ llen :: List -> Nat @-}
llen :: List -> Int
llen Nil        = 0
llen (Cons h t) = 1 Prelude.+ llen t

{-@ reflect beqList @-}
beqList :: List -> List -> Bool
beqList (Cons x xs) (Cons y ys) = x == y && beqList xs ys
beqList Nil         Nil         = True
beqList Nil         (Cons y ys) = False
beqList (Cons x xs) Nil         = False


{-@ testBeqList2 :: { beqList (Cons 1 Nil) (Cons 1 Nil) } @-}
testBeqList2  = trivial

{-@ testBeqList3 :: { beqList (Cons 1 (Cons 2 Nil)) (Cons 1 (Cons 3 Nil)) == False } @-}
testBeqList3  = trivial
