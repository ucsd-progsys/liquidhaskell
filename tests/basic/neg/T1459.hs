import qualified Data.ByteString.Lazy as BL

bar2 :: BL.ByteString -> Int
bar2 = sum . map fromIntegral . BL.unpack . BL.tail
