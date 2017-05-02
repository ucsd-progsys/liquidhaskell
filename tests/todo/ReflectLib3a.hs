{-@ LIQUID "--totality"                            @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module ReflectLib3a where

import Language.Haskell.Liquid.ProofCombinators

{-@ data Day = Mon | Tue @-}
data Day = Mon | Tue

{-@ reflect next @-}
next :: Day -> Day
next Mon = Tue
next Tue = Mon

{-@ testFAIL :: { next Mon == Tue } @-}
testFAIL = trivial 
