{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module T1289 where

{-@ reflect intId @-}
intId :: Int -> Int
intId 0 = 0
intId x = x

thm1 :: Int -> () 
{-@ thm1 :: x:Int -> {intId x = x} @-}
thm1 x = if x == 0 then () else ()


{-@ measure charId @-}
charId :: Char -> Char
charId 'a' = 'a'
charId x = x
