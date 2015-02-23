module DBC where

import GHC.CString  -- This import interprets Strings as constants!


bar :: () -> String 
{-@ bar :: () -> {x:String | x = foo} @-}
bar _ = "foo"
