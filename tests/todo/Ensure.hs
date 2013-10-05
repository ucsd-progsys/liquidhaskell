module Ensure where

{-@ qualif Diff(v:int,l:int,d:int): v = l-d @-}

{-@ encodeUtf8 :: Nat -> Nat @-}
encodeUtf8 :: Int -> Int
encodeUtf8 len = start 1 0
  where
    start size n0 = go (len-n0) n0
      where
        go :: Int -> Int -> Int
        go d n
          | n == len  = n
          | otherwise = ensure 1 (\n -> go (d-1) (n+1))
              where
                ensure :: Int -> (Int -> Int) -> Int
                ensure k cont
                  | size-k >= n = cont n
                  | otherwise   = start (size*2) n
