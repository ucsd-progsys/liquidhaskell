-- GOAL: get the `assume plus` in Prelude to be qualified to `assume LH.plus` ...

module Assume00 where 

import Language.Haskell.Liquid.Prelude

data Thing = Thing 

{-@ plus :: Thing -> Thing -> {v:Thing | false} @-}
plus :: Thing -> Thing -> Thing 
plus _ _ = Thing 

