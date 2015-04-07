module spec GHC.Int where

embed GHC.Int.Int8  as int
embed GHC.Int.Int16 as int
embed GHC.Int.Int32 as int
embed GHC.Int.Int64 as int

type Nat64 = {v:GHC.Int.Int64 | v >= 0}
