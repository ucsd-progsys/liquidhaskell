{-@ LIQUID "--expect-error-containing=Specified type does not refine Haskell type for `BadDataConType1.fldY`" @-}
{-@ LIQUID "--expect-error-containing=Illegal type specification for `BadDataConType1.fldY`" @-}
module BadDataConType1 where

{-@ data T = C { fldX :: Int, fldY :: String } @-}

data T = C { fldX :: Int, fldY :: Int }
