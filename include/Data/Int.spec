module spec Data.Int where

embed Int32 as int
embed Int64 as int

type Nat64 = {v:Int64 | v >= 0}
