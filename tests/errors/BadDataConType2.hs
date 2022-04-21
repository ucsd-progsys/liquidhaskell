module BadDataConType2 where

{-@ data T = C { fldX :: Int } @-}

data T = C { fldX :: Int, fldY :: Int }
