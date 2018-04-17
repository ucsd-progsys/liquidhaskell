{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

{-@ reflect intId @-}
intId :: Int -> Int
intId 0 = 0
intId x = x

thm1 :: Int -> () 
{-@ thm1 :: x:Int -> {intId x = x} @-}
thm1 x = ()

