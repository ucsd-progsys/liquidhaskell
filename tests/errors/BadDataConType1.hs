{-@ LIQUID "--expect-error-containing=Specified type does not refine Haskell type for `BadDataConType1.C`" @-}
module BadDataConType1 where

{-@ data T = C { fldX :: Int, fldY :: String } @-}

data T = C { fldX :: Int, fldY :: Int }
