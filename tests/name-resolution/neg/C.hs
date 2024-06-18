{-@ LIQUID "--expect-error-containing=Unknown type constructor `A.Ty`" @-}
module C where

import B

-- This is an instance of Liquid Haskell's resolving names twice.
-- `B.Exp` uses `Ty` which is defined in module A
-- but it is somehow out of scope when compiling module C.
