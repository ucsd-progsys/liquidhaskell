module Issue595 where

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

-- The above data declaration should give us the following refined types
-- for the record selectors

{- vec :: x:Test -> {v:Thing | v = vec x} -}
{- x0  :: x:Test -> {v:Bool  | v = x0 x  && ((len (vec x) < 1) => Prop v) } -}

example :: Test -> ()
example t =
    if x0 t
    then ()
    else vec t !! 0
