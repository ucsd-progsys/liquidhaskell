module spec Foreign.C.Types where

-- measure cSizeInt :: CSize -> GHC.Types.Int
-- invariant {v: CSize | (cSizeInt v) >= 0}

embed CSize  as int
embed CULong as int
