{-@ LIQUID "--totality"                            @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module ReflectClient3a where

import Language.Haskell.Liquid.ProofCombinators

import ReflectLib3

-- stupidity = [ undefined gapp ] -- , undefined Nil ]

{-@ test5 :: { gapp Nil = Nil } @-}
test5 = ()
