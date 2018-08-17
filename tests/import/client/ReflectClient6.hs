{-@ LIQUID "--reflection" @-} 
{-@ LIQUID "--ple"        @-} 

module ReflectClient6 where

import Language.Haskell.Liquid.NewProofCombinators

import ReflectLib6

{-@ testOK :: { next Mon == Tue } @-}
testOK = next Mon === Tue *** QED

{-@ testFAIL :: { next Tue == Mon } @-}
testFAIL = trivial 

