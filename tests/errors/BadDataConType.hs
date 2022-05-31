{-@ LIQUID "--expect-error-containing=\"Illegal type specification for `BadDataConType.fldY`\"" @-}
module BadDataConType where

{-@ data T = C { fldX :: Int, fldY :: Bool } @-}

data T = C { fldX :: Int, fldY :: Int }
