{-@ LIQUID "--exact-data-con"                      @-}
{- LIQUID "--automatic-instances=liquidinstances" @-}

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

-- THIS DOES NOT WORK, but it DOES work if we remove the
-- type parameter from `List`. However it DOES work if we
-- put this back into ReflectLib3.hs
{-@ test4 :: { lDay Nil == Mon } @-}
test4 = lDay Nil ==. Mon *** QED
