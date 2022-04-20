module BadDataConType1 where

{-@ data T = C { fldX :: Int, fldY :: String } @-}

data T = C { fldX :: Int, fldY :: Int }
