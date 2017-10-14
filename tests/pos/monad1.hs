module Monad where

{-@ LIQUID "--no-pattern-inline" @-}

-- create :: Int -> (Ptr Word8 -> IO ()) -> IO ByteString
create l = do
    fp <- mallocByteString l
    return ()

data P a = P a

mallocByteString :: a -> IO (P a)
mallocByteString l = undefined
