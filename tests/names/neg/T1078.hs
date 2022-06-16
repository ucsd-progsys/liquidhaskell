{-@ LIQUID "--expect-any-error" @-}
module T1078 where

-- TODO-REBARE: filter gsAsmSigs to ONLY keep USED vars.

-- needed to bring `bslen` into scope
-- import qualified Data.ByteString

import qualified Data.ByteString.Char8
import Data.Word

example :: Char
example = Data.ByteString.Char8.head Data.ByteString.Char8.empty
