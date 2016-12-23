module DBC where

import GHC.CString  -- This import interprets Strings as constants!

import Data.Set

{-@ prop1 :: {v:Bool | v } @-}
prop1 :: Bool
prop1 = foo1 /= foo2 
  where foo1 = "foo"
        foo2 = "bar"
