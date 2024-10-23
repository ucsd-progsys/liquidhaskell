{-# OPTIONS_GHC -Wno-unused-imports #-}
-- | This is an instance of Liquid Haskell's resolving names twice.
-- `B.Exp` uses `Ty` which is defined in module A
-- but it used to be out of scope when compiling module C before
-- fixing renaming bugs.
module C where

import B

