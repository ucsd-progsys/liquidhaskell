module ImportedReflect where

import B 
import A 

{-@ theorem :: x:Bar -> {bar x = bar x} @-}
theorem :: Bar -> ()
theorem _ = ()