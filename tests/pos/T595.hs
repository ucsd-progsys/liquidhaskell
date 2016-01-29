module T595 where

import Data.Vector

{-@
data Test = Test
    { v  :: Vector ()
    , x0 :: { x0 : Bool | vlen v < 1 ==> Prop x0 }
    }
@-}

{-@ x0 :: t:Test -> {r:_ | r == x0 t } @-}

data Test = Test
    { v  :: Vector ()
    , x0 :: Bool
    }

example :: Test -> ()
example t =
    if x0 t
    then ()
    else v t ! 0
