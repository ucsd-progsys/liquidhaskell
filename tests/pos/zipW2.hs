module ListSort where


foo :: [Int] -> [Int]
foo zs = zipWith (+) zs zs
