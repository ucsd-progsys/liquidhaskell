{-@ LIQUID "--exact-data-con" @-}

module T1102_LibX where

import T1102_LibY 

{-@ theorem :: x:Bar -> {bar x = bar x} @-}
theorem :: Bar -> ()
theorem _ = ()
