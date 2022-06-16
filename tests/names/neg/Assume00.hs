{-@ LIQUID "--expect-any-error" @-}
-- GOAL: get the `assume plus` in Prelude to be qualified to `assume LH.plus` ...

module Assume00 where 

import Language.Haskell.Liquid.Prelude

data Thing = Thing 

{-@ plus :: x:Thing -> Thing -> {v:Thing | false } @-}
plus :: Thing -> Thing -> Thing 
plus x _ = x

