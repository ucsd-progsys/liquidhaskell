module Vec0 where

absoluteSum vec   = if 0 < n then goxx 0 0 else 0
  where
    goxx acc i 
      | i /= n    = goxx (acc + i) (i + 1)
      | otherwise = acc 
    n             = length vec


