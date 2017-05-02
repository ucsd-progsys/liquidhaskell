
{-@ LIQUID "--exact-data-con"                      @-}
{- LIQUID "--higherorder"                         @-}
{-@ LIQUID "--totality"                            @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module ReflectLib3 where

import Language.Haskell.Liquid.ProofCombinators

-- | Lists ---------------------------------------------------------------------

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
{-@ llen :: xs:List a -> {v:Nat | v = llen xs} @-}
llen :: List a -> Int
llen Nil        = 0
llen (Cons h t) = 1 + llen t

{-@ reflect lSize @-}
lSize :: List a -> Int
lSize Nil        = 0
lSize (Cons h t) = 1 + lSize t

{-@ reflect lDay @-}
lDay Nil         = Mon 
lDay (Cons x xs) = Tue

-- TODO: NEEDED for the IMPORT to work.
{-@ invariant { v:List a | 0 <= llen v } @-}

{-@ reflect app @-}
app :: List a -> List a -> List a
app Nil         ys = ys
app (Cons x xs) ys = Cons x (app xs ys)

--------------------------------------------------------------------------------
{-@ thmAppLen :: xs:List a -> ys:List a ->
      { llen (app xs ys) == llen xs + llen ys}
  @-}
thmAppLen :: List a -> List a -> Proof
thmAppLen Nil ys
  =   llen (app Nil ys)
  ==. llen ys
  ==. llen Nil + llen ys
  *** QED
thmAppLen (Cons x xs) ys
  =   llen (app (Cons x xs) ys)
  ==. llen (Cons x (app xs ys))
  ==. 1 + llen (app xs ys)
      ? thmAppLen xs ys
  ==. 1 + llen xs + llen ys
  ==. llen (Cons x xs) + llen ys
  *** QED
