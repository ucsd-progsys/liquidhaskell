module spec Data.Int where

embed Data.Int.Int8  as int
embed Data.Int.Int16 as int
embed Data.Int.Int32 as int
embed Data.Int.Int64 as int

//  type Nat64 = {v:Data.Int.Int64 | v >= 0}
