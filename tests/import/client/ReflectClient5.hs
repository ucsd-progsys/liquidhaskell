{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module ReflectClient5 where

import Language.Haskell.Liquid.ProofCombinators

import ReflectLib5

{-@ test5 :: { gapp Nil = Nil } @-}
test5 = ()
