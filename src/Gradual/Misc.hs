{-# LANGUAGE TupleSections         #-}

module Gradual.Misc where 

-------------------------------------------------------------------------------
-- | Mapping ------------------------------------------------------------------
-------------------------------------------------------------------------------

mapThd3 :: (c -> d) -> (a, b, c) -> (a, b, d)
mapThd3 f (x, y, z) = (x, y, f z)


-------------------------------------------------------------------------------
-- | Combining ----------------------------------------------------------------
-------------------------------------------------------------------------------


flatten :: [(k,(i,[v]))] -> [[(k,v)]]
flatten kvs = allCombinations ((\(k,(_,vs)) -> (k,) <$> vs)<$> kvs)

expand :: (a -> [a]) -> [a] -> [[a]]
expand f xs = allCombinations (f <$> xs)

expand2 :: (b -> [b]) -> [(a, b)] -> [[(a,b)]]
expand2 f xs = zip x1s <$> allCombinations x2s
  where
    (x1s,x2s) = unzip ((\(x,y) -> (x,f y)) <$> xs)

expand3 :: (c -> [c]) -> [(a,b,c)] -> [[(a,b,c)]]
expand3 f xs = zip3 x1s x2s <$> allCombinations x3s
  where
    (x1s,x2s,x3s) = unzip3 ((\(x,y,z) -> (x,y,f z)) <$> xs)

{-@ allCombinations :: xss:[[a]] -> [{v:[a]| len v == len xss}] @-}
allCombinations :: [[a]] -> [[a]]
allCombinations xs = assert (and . map (((length xs) == ) . length)) $ go xs
  where
   go []          = [[]]
   go [[]]        = []
   go ([]:_)      = []
   go ((x:xs):ys) = ((x:) <$> go ys) ++ go (xs:ys)

   assert b x = if b x then x else error "allCombinations: assertion violation"