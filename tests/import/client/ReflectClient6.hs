{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module ReflectClient6 where

import Language.Haskell.Liquid.ProofCombinators

import ReflectLib6

{-@ testOK :: { next Mon == Tue } @-}
testOK = next Mon ==. Tue *** QED

{-@ testFAIL :: { next Tue == Mon } @-}
testFAIL = trivial 

