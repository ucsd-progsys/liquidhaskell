{-@ LIQUID "--exact-data-con" @-}

module T1102_LibX where

import T1102_LibY 
-- import T1102_LibZ 
-- zink = fooA 

{-@ theorem :: x:Bar -> {bar x = bar x} @-}
theorem :: Bar -> ()
theorem _ = ()
