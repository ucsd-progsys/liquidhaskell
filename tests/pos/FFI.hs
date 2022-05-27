{-# LANGUAGE ForeignFunctionInterface #-}
module FFI where

import Foreign.C.Types

{-@ embed CInt as int @-}
{-@ embed Integer as int @-}

{-@ assume c_foo :: x:{CInt | x > 0} -> IO {v:CInt | v = x} @-}
foreign import ccall unsafe "foo.c foo" c_foo
  :: CInt -> IO CInt

main :: IO ()
main = print . fromIntegral =<< c_foo 1
