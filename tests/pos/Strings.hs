module DBC where

import GHC.CString  -- This import interprets Strings as constants!


bar :: () -> String 
{-@ bar :: () -> {x:String | x = unpack "foo" && len x >= 0} @-}
bar _ = "foo"


{-@ prop :: {v:Bool | Prop v <=> true} @-}
prop :: Bool
prop = foo1 == foo2 
  where foo1 = "foo"
        foo2 = "foo"