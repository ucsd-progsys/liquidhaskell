module Assume01 where

import qualified Data.ByteString as BS

{-@ assume BS.head    :: BS.ByteString -> _ @-}

junk = BS.head
