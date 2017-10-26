{-# LANGUAGE TupleSections         #-}

module Gradual.Misc where 

import Control.Monad (filterM)

-------------------------------------------------------------------------------
-- | Mapping ------------------------------------------------------------------
-------------------------------------------------------------------------------

mapThd3 :: (c -> d) -> (a, b, c) -> (a, b, d)
mapThd3 f (x, y, z) = (x, y, f z)

mapSndM :: Functor m => (b -> m c) -> (a,b) -> m (a, c)
mapSndM f (x,y) = (x,) <$> f y


mapMWithLog :: String -> (a -> IO b) -> [a] -> IO [b]
mapMWithLog msg f xs = go 1 xs 
  where
    n = length xs 

    go _ [] = return []
    go i (x:xs) = do 
      putStrLn (msg ++ " [" ++ show i ++ "/" ++ show n ++ "]...") 
      r  <- f x 
      rs <- go (i+1) xs 
      return (r:rs)

-------------------------------------------------------------------------------
-- | Powersets ----------------------------------------------------------------
-------------------------------------------------------------------------------

powersetUpTo :: Int -> [a] -> [[a]]
powersetUpTo 0 _  = [] 
powersetUpTo 1 xs = (:[]) <$> xs
powersetUpTo i xs = filter ((i >=) . length) $ filterM (const [False, True]) xs

-------------------------------------------------------------------------------
-- | Combining ----------------------------------------------------------------
-------------------------------------------------------------------------------


flatten :: [(k,(i,[v]))] -> [[(k,(i, v))]]
flatten kvs = allCombinations ((\(k,(i,vs)) -> ((k,) . (i,)) <$> vs)<$> kvs)

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