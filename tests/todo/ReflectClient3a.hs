
{-@ LIQUID "--totality"                            @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module ReflectClient3 where

import Language.Haskell.Liquid.ProofCombinators
import ReflectLib3

forceImports = [ undefined next
               , undefined llen
               , undefined lDay
               , undefined app
               ]

{-@ test2 :: { next Mon == Tue } @-}
test2 = next Mon ==. Tue *** QED

{-@ test4 :: { lDay Nil == Mon } @-}
test4 = lDay Nil ==. Mon *** QED

{-@ test3 :: { llen Nil == 0 } @-}
test3 = trivial
-- {- thmAppSize :: xs:List a -> ys:List a ->
      -- { lSize (app xs ys) == lSize xs + lSize ys}
  -- -}
-- thmAppSize :: List a -> List a -> Proof
-- thmAppSize Nil ys
  -- =   lSize (app Nil ys)
  -- ==. lSize ys
  -- ==. lSize Nil + lSize ys
  -- *** QED

--  thmAppLen (Cons x xs) ys
  --  =   llen (app (Cons x xs) ys)
  --  ==. llen (Cons x (app xs ys))
  --  ==. 1 + llen (app xs ys)
      --  ? thmAppLen xs ys
  --  ==. 1 + llen xs + llen ys
  --  ==. llen (Cons x xs) + llen ys
  --  *** QED

--
--------------------------------------------------------------------------------
-- Random Debug Stuff
--------------------------------------------------------------------------------

{-@ zen :: xs:List a -> {v:Nat | v = llen xs} @-}
zen :: List a -> Int
zen Nil        = 0
zen (Cons h t) = 1 + zen t

-- THIS FAILS
{-@ zoo :: List a -> {v:Int | v == 0} @-}
zoo :: List a -> Int
zoo Nil         = llen Nil
zoo (Cons x xs) = zoo xs
