module Fooo where


stupid x y = go x
  where go [] = []
        go (x:xs) = y x : go xs
