{-@ LIQUID "--expect-any-error" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module T1289 where

{-@ reflect intId @-}
intId :: Int -> Int
intId 0 = 1
intId x = x

{-@ thm1 :: x:Int -> {intId x = x} @-}
thm1 :: Int -> () 
thm1 x = ()

{- measure bintId @-}
bintId :: Int -> Int
bintId 0 = 0
bintId x = x


