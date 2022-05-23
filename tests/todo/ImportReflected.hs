module ImportedReflect where

import BLib

{-@ theorem :: x:Bar -> {bar x = bar x} @-}
theorem :: Bar -> ()
theorem _ = ()
