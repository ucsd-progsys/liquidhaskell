module TakeMap where

import           Prelude                 hiding ( map
                                                , take
                                                )
import           Language.Haskell.Liquid.ProofCombinators

{-@ reflect map @-}
map :: (Int -> Int) -> [Int] -> [Int]
map _ []       = []
map f (x : xs) = f x : map f xs

{-@ reflect take @-}
take :: Int -> [Int] -> [Int]
take n _ | n <= 0 = []
take _ []         = []
take n (x : xs)   = x : take (n - 1) xs

--- Unary

{-@ commMapTake :: n:Int -> g:(Int -> Int) -> l:[Int] -> {map g (take n l) = take n (map g l)} @-}
commMapTake :: Int -> (Int -> Int) -> [Int] -> ()
commMapTake _ _ []         = ()
commMapTake n _ _ | n <= 0 = ()
commMapTake n g (x : xs)   = commMapTake (n - 1) g xs

--- Relational

mapTake :: Int -> (Int -> Int) -> [Int] -> [Int]
mapTake n g l = map g (take n l)

takeMap :: Int -> (Int -> Int) -> [Int] -> [Int]
takeMap n g l = take n (map g l)

{-@ reflect prefix @-}
prefix :: [Int] -> [Int] -> Bool
prefix [] _                       = True
prefix (x : xs) (y : ys) | x == y = prefix xs ys
prefix _ _                        = False

{-@ reflect gPrefix @-}
gPrefix :: (Int -> Int) -> [Int] -> [Int] -> Bool
gPrefix g xs ys = prefix (map g xs) ys

{-@ relational take ~ map :: n:Int -> xs:[Int] -> [Int]
                           ~ g:(Int -> Int) -> ys:[Int] -> [Int]
                          ~~ true => xs = ys => 
                              TakeMap.gPrefix g (r1 n xs) (r2 g ys) &&
                                len (r1 n xs) = TakeMap.min n (len xs) &&
                                  len (r2 g ys) = len ys @-}

{-@ relational map ~ take :: g:(Int -> Int) -> xs:[Int] -> [Int]
                           ~ n:Int -> ys:[Int] -> [Int]
                          ~~ true => TakeMap.gPrefix g xs ys && n >= len xs => 
                              TakeMap.prefix (r1 g xs) (r2 n ys) &&
                                len (r1 g xs) = len xs &&
                                  len (r2 n ys) = TakeMap.min n (len ys) @-}

{-@ relational mapTake ~ takeMap 
      :: n1:Int -> g1:(Int -> Int) -> l1:[Int] -> [Int] ~ n2:Int -> g2:(Int -> Int) -> l2:[Int] -> [Int]
      ~~ n1 = n2 => g1 = g2 => l1 = l2 => 
          TakeMap.prefix (r1 n1 g1 l1) (r2 n2 g2 l2) && 
            len (r1 n1 g1 l1) = TakeMap.min n1 (len l1) &&
              len (r2 n2 g2 l2) = TakeMap.min n2 (len l2) @-}

--- Utils

{-@ reflect min @-}
min :: Int -> Int -> Int
min a b = if a <= b then a else b
