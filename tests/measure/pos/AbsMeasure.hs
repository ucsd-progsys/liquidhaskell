
module AbsMeasure where

------------------------------------------------------------
{-@ measure foo :: Int -> Int @-}

{-@ prop :: x:Int -> {v:Int | foo v = foo x} @-}
prop :: Int -> Int 
prop x = x 
------------------------------------------------------------
{-@ measure fooBool :: Int -> Bool @-}

{-@ propBool :: x:Int -> {v:Int | fooBool v = fooBool x} @-}
propBool :: Int -> Int 
propBool x = x 
------------------------------------------------------------

-- imports = ( False )
