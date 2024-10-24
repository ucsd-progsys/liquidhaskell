-- Example giving the equivalent code to what is generated by opaque reflection when `filter` and `even` are not already reflected

{-@ LIQUID "--reflection"      @-}

module OpaqueRefl02 where

{-@ measure filter :: (a -> Bool) -> [a] -> [a] @-}
{-@ assume filter :: p:(a -> Bool) -> xs:[a] -> {v : [a] | v == filter p xs && len v <= len xs} @-}
{-@ measure even :: a -> Bool @-}
{-@ assume even :: x:a -> {VV : Bool | VV == even x} @-}

{-@ reflect keepEvens @-}
keepEvens :: [Int] -> [Int]
keepEvens = filter even
