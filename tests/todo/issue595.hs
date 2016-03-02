-- module Issue595 where

import Data.Vector

data Test = Test
    { vec  :: Thing
    , x0   :: Bool
    }

type Thing = [()] -- Vector ()

{-@
data Test = Test
    { vec  :: Thing
    , x0   :: { x0 : Bool | len vec < 1 ==> Prop x0 }
    }
@-}

{-@ vec  :: t:Test -> {r:Thing | r = vec t } @-}
{-@ x0   :: t:Test -> {r:Bool  | r = x0 t } @-}

example :: Test -> ()
-- NOTE: this works 
-- example t@(Test _ _) =
example t =
    if x0 t
    then ()
    else vec t !! 0
