module DBC where

import GHC.CString  -- This import interprets Strings as constants!


import Data.Set
{-
bar :: () -> String 
{- bar :: () -> {x:String | x = unpack "foo" && len x >= 0} @-}
bar _ = "foo"


{- prop :: {v:Bool | Prop v <=> true} @-}
prop :: Bool
prop = foo1 == foo2 
  where foo1 = "foo"
        foo2 = "foo"
-}
{- 

data Foo = FFFF | QQQQ deriving Eq

{-@ prop2 :: {v:Bool | Prop v <=> true} @-}
prop2 :: Bool
prop2 = foo1 /= foo2 
  where foo1 = FFFF
        foo2 = QQQQ


{-@ prop3 :: {v:[String] | listElts v ~~ Set_sng "xx"} @-}
prop3 :: [String]
prop3 = ["xx"]
-}
{-@ prop1 :: {v:Bool | Prop v <=> true} @-}
prop1 :: Bool
prop1 = foo1 /= foo2 
  where foo1 = "foo"
        foo2 = "bar"
