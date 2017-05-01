
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}
{-@ LIQUID "--totality"                            @-}

module ReflectClient3 where

import Language.Haskell.Liquid.ProofCombinators
import ReflectLib3

stupidity = [ undefined next
            , undefined app
            ]

{-@ test2 :: { next Mon == Tue } @-}
test2 = trivial

{-@ test3 :: { llen Nil == 0 } @-}
test3 = trivial

{-@ thmAppLen :: xs:List a -> ys:List a ->
      { llen (app xs ys) == llen xs + llen ys}
  @-}
thmAppLen :: List a -> List a -> Proof
thmAppLen Nil         ys = trivial
thmAppLen (Cons x xs) ys = thmAppLen xs ys
