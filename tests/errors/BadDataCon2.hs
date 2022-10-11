{-@ LIQUID "--expect-error-containing=GHC and Liquid specifications have different numbers of fields for `BadDataCon2.Cuthb`" @-}
module BadDataCon2 where

{-@ data T = Cuthb { fldX :: Int, fldY :: Int } @-}

data T = Cuthb { fldX :: Int }
