module Fixme where

import           Prelude                 hiding ( map )

{-@ reflect diff @-}
{-@ diff :: xs:[Int] -> ys:{[Int]|len ys == len xs} -> Int @-}
diff :: [Int] -> [Int] -> Int
diff (x : xs) (y : ys) | x == y = diff xs ys
diff (x : xs) (y : ys) | x /= y = 1 + diff xs ys
diff _ _                        = 0

{-@ reflect map @-}
map :: (Int -> Int) -> [Int] -> [Int]
map _ []       = []
map f (x : xs) = f x : map f xs

{-@ relational map ~ map :: {f1:(x1:_ -> _) -> xs1:_ -> _ ~ f2:(x2:_ -> _) -> xs2:_ -> _ 
                         | true :=> len xs1 = len xs2 && f1 = f2 :=> Fixme.diff xs1 xs2 >= Fixme.diff (r1 f1 xs1) (r2 f2 xs2)} @-}

{-@ relMapMap_rga :: f1:(x1:Int -> Int) -> f2:(x2:Int -> Int) -> xs1:[Int] -> xs2:{VV : [Int] | f1 == f2 && len xs1 == len xs2} 
                  -> {VV : () | Fixme.diff xs1 xs2 >= Fixme.diff (Fixme.map f1 xs1) (Fixme.map f2 xs2)} @-}
relMapMap_rga :: (Int -> Int)
                -> (Int -> Int)
                -> [Int]
                -> [Int]
                -> ()
relMapMap_rga ds_d1mml ds_d1mm ds_d1mnl ds_d1mn =
    case ds_d1mnl of
        [] ->
            case ds_d1mn of
                [] -> ()
                (:) x xs -> ()

        (:) xl xsl ->
            case ds_d1mn of
                [] -> relMapMap_rga ds_d1mml ds_d1mm xsl [] `const` relMapMap_rga ds_d1mml ds_d1mm xsl []
                (:) x xs -> -- (\ _ _ _ _ -> ()) ((\ _ _ -> ()) xl x) ((\ _ _ -> ()) xl x) 
                            -- (
                                relMapMap_rga ds_d1mml ds_d1mm xsl xs `const` relMapMap_rga ds_d1mml ds_d1mm xsl xs

