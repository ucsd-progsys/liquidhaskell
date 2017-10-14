module ImportedReflect where

import B 

{-@ theorem :: x:Bar -> {bar x = bar x} @-}
theorem :: Bar -> ()
theorem _ = ()