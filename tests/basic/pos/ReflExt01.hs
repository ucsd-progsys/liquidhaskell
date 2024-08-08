-- | test reflection away from the source, using the unfoldings of the interface files

{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--reflection" @-}

module ReflExt01 where

{-@ reflect uncurry @-}

{-@ reflect otherFn @-}
otherFn :: (Int , Int) -> Int
otherFn = uncurry myAdd

{-@ reflect myAdd @-}
myAdd :: Int -> Int -> Int
myAdd a b = a + b + 1
