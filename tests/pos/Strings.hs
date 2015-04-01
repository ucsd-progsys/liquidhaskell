module DBC where

import GHC.CString  -- This import interprets Strings as constants!


bar :: () -> String 
{-@ bar :: () -> {x:String | x = unpack "foo" && len x >= 0} @-}
bar _ = "foo"
