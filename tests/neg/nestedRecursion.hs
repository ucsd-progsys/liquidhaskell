module Map (radicals) where

radicals :: Int -> [a]
radicals n = [ foo (radicals n) i | i <- [1..]]

foo = undefined
