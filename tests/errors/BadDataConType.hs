module BadDataConType where

{-@ data T = C { fldX :: Int, fldY :: Bool } @-}

data T = C { fldX :: Int, fldY :: Int }
