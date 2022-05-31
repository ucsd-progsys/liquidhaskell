{-@ LIQUID "--expect-any-error" @-}
module T1459 where

-- https://github.com/ucsd-progsys/liquidhaskell/issues/1459

import qualified Data.ByteString.Lazy as BL

bar2 :: BL.ByteString -> Int
bar2 = sum . map fromIntegral . BL.unpack . BL.tail
