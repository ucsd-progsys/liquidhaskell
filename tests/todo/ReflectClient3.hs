
{-@ LIQUID "--totality"                            @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module ReflectClient3 where

import Language.Haskell.Liquid.ProofCombinators

import ReflectLib3

-- THIS IS NEEDED TO BRING THE NAMES INTO SCOPE FOR GHC ...
forceImports = [ undefined next
               , undefined lDay
               ]

-- THIS WORKS
{-@ test2 :: { next Mon == Tue } @-}
test2 = next Mon ==. Tue *** QED

-- THIS DOES NOT
{-@ test4 :: { lDay Nil == Mon } @-}
test4 = lDay Nil ==. Mon *** QED
