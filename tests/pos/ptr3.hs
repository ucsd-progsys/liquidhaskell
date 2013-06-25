
-- WHY ON EARTH IS THAT LIQUIDASSERT NEEDED?!!!!

{-@ split :: Word8 -> ByteStringNE -> [ByteString] @-}
split :: Word8 -> ByteString -> [ByteString]
-- split _ (PS _ _ 0) = []
split w (PS xanadu s l) = inlinePerformIO $ withForeignPtr xanadu $ \pz -> do
    let p   = liquidAssert (fpLen xanadu == pLen pz) pz
    let ptr = p `plusPtr` s

        STRICT1(loop)
        loop n =
            let q = inlinePerformIO $ memchr (ptr `plusPtr` n)
                                           w (fromIntegral (l-n))
            in if isNullPtr q {- LIQUID q == nullPtr -}
                then [PS xanadu (s+n) (l-n)]
                else let i' = q `minusPtr` ptr 
                         i  = liquidAssert (i < l) i'       -- LIQUID MYSTERY: why is assert NEEDED HERE (it is!)
                     in PS xanadu (s+n) (i-n) : loop (i+1)

    return (loop 0)


