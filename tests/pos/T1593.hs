
module T1593 where

{-@ LIQUID "--reflection"     @-}

-- not ok
data Thing0 m = Thing
  { t0 :: (m Int -> Int) -> Int
  }

-- not ok
data Thing1 m = Thing1
  { t1 :: (Int -> m Int) -> Int
  }

-- ok
data Thing2 m = Thing2
  { t2 :: Int -> m Int -> Int
  }
