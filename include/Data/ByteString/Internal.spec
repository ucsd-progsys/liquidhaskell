module spec Data.ByteString.Internal where

data ByteString
    = PS (playload :: (ForeignPtr Word8)) 
         (offset   :: Int)
         (len      :: {v : Int | v >= 0})
