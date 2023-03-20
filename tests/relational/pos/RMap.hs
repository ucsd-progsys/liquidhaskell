{-@ LIQUID "--relational-hint" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module RMap where
import Prelude hiding (map)

type List a = [a]

{-@ reflect map @-}
map :: (Int -> Int) -> List Int -> List Int
map _ [] = []
map f (x:xs) = f x:map f xs

--- Proof ---
{-@ relational map ~ map ::
            { f1:(x1:Int -> Int) -> xs1:List Int -> List Int 
            ~ f2:(x2:Int -> Int) -> xs2:List Int -> List Int 
            | !(true :=> true) 
                :=> !(len xs1 = len xs2)
                :=> len (r1 f1 xs1) = len (r2 f2 xs2) } @-}
--- End ---