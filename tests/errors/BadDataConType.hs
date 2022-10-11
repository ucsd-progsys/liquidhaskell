{-@ LIQUID "--expect-error-containing=Illegal type specification for `BadDataConType.fldY`" @-}
{-@ LIQUID "--expect-error-containing=Specified type does not refine Haskell type for `BadDataConType.fldY`" @-}
module BadDataConType where

{-@ data T = C { fldX :: Int, fldY :: Bool } @-}

data T = C { fldX :: Int, fldY :: Int }
