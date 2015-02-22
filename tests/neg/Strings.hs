module DBC where

import GHC.CString  -- This import interprets Strings as constants!


bar :: () -> String 
{-@ bar :: () -> {x:String | x = boo} @-}
bar _ = "foo"

boo :: String
boo = "boo"
