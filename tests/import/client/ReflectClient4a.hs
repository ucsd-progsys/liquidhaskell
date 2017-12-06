{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module ReflectClient4a where

import Language.Haskell.Liquid.ProofCombinators

import ReflectLib4 

stupidity = [ undefined gapp ]

{-@ test1 :: { llen Nil == 0 } @-}
test1 = ()

{-@ test2 :: { llen (Cons 2 Nil) == 1 } @-}
test2 = ()

{-@ test3 :: { llen (Cons 1 (Cons 2 Nil)) == 2 } @-}
test3 = ()

{-@ test4 :: { app Nil Nil == Nil } @-}
test4 = () 

{-@ test5 :: { gapp Nil = Nil } @-}
test5 = ()


-- {- thmAppLen :: xs:List a -> ys:List a ->
      -- { llen (app xs ys) == llen xs + llen ys}
  -- @-}
-- thmAppLen :: List a -> List a -> Proof
-- thmAppLen Nil         ys = trivial
-- thmAppLen (Cons x xs) ys = thmAppLen xs ys
