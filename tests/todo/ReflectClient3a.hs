
{-@ LIQUID "--totality"                            @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module ReflectClient3 where

import Language.Haskell.Liquid.ProofCombinators
import ReflectLib3

{-@ testOK :: { next Mon == Tue } @-}
testOK = next Mon ==. Tue *** QED

{-@ testFAIL :: { next Tue == Mon } @-}
testFAIL = trivial 

