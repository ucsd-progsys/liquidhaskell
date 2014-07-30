{-# LANGUAGE ForeignFunctionInterface #-}
module Main where

import Foreign.C.Types

{-@ c_foo :: x:{CInt | v > 0} -> IO {v:CInt | v = x} @-}
foreign import ccall unsafe "static foo.c foo" c_foo
  :: CInt -> IO CInt

main :: IO ()
main = print . fromIntegral =<< c_foo 1
