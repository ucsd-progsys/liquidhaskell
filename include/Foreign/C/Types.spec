module spec Foreign.C.Types where

-- measure cSizeInt :: CSize -> GHC.Types.Int
-- invariant {v: CSize | (cSizeInt v) >= 0}

embed Foreign.C.Types.CInt   as int
embed Foreign.C.Types.CSize  as int
embed Foreign.C.Types.CULong as int
