module ZipW2 where


foo :: [Int] -> [Int]
foo zs = zipWith (+) zs zs
