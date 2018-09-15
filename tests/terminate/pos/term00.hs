
zoo :: Int -> Int
zoo n 
  | 0 < n     = n + zoo (n-1)
  | otherwise = 0 
