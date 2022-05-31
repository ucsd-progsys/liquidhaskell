{-@ LIQUID "--expect-error-containing=different numbers of fields for `BadDataConType2.C`" @-}
module BadDataConType2 where

{-@ data T = C { fldX :: Int } @-}

data T = C { fldX :: Int, fldY :: Int }
