
-- needed to bring `bslen` into scope
-- import qualified Data.ByteString

import qualified Data.ByteString.Char8

example :: Char
example = Data.ByteString.Char8.head Data.ByteString.Char8.empty
