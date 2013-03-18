module spec Foreign.C.Types where

measure asInt :: CSize -> GHC.Types.Int

invariant {v: CSize | (asInt v) >= 0}

