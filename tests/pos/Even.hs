module Even where


-- TODO BUG WHEN TYSIG IS REMOVED

isEven :: Int -> Bool
isEven 0 = True
isEven n = isOdd  $ n-1

isOdd  m = isEven $ m-1
