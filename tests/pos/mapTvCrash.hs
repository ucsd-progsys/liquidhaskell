module Foo (foo) where

import Foreign.ForeignPtr

{-@ foo :: FinalizerPtr a -> a @-}
foo :: FinalizerPtr a -> a
foo = undefined
