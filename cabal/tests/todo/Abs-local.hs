
abs0   :: Int -> Int 
abs0 x = if x > 0 then x else (-x)

abs1   :: Int -> Int 
abs1 x | x > 0     = x 
       | otherwise = -x


abs2 x = if x > 0 then x else (-x)

abs3 x | x > 0     = x 
       | otherwise = -x

main = do print $ abs0 2
          print $ abs1 2
          print $ abs2 2
          print $ abs3 2
          print $ abs0 (-2)
          print $ abs1 (-2)
          print $ abs2 (-2)
          print $ abs3 (-2)
