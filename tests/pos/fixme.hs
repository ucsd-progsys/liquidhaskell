module Data.Set.Splay  where

insert :: a -> a
insert x = l
  where
    (l,w) = split x

-- this crashes
split :: a -> (a, Bool)
split x = (x,False)

-- this does not crash
-- split :: a -> (a, Int)
-- split x = (x,1)

