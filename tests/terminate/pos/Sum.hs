
module Sum where

ssum :: Num a => [a] -> a
ssum []       = 0
ssum [x]      = x
ssum (x:xs)   = x + ssum xs
