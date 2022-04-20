{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--extensionality" @-}
{-@ LIQUID "--ple"            @-}

module T1577 where

-- | 1 . ints

{-@ reflect plus1 @-}
{-@ reflect plus1' @-}
plus1, plus1' :: Int -> Int 
plus1 x = x + 1 
plus1' x = 1 + x

{-@ thm1 :: () -> { plus1' == plus1 } @-}
thm1 :: () -> ()
thm1 _ = () 

{-@ reflect first @-}
first :: (a -> b) -> (a, c) -> (b, c)
first f (x,y) = (f x, y)

-- | 2. compose

{-@ thm2 :: f:(a -> b) -> g:(b -> c) -> { (first g) . (first f) == first (g . f) } @-}
thm2 :: (a -> b) -> (b -> c) -> ()
thm2 _ _ = ()

-- | 3. imply 

{-@ thm3 :: f:(a -> b) -> g:(a -> b) -> { first f == first g => f == g } @-}
thm3 :: (a -> b) -> (a -> b) -> ()
thm3 _ _ = ()
