-- Tests that annotations from GHC.Types are available
-- when using the Ord class.
module T2198 where

g :: Int -> Bool
g x = x >= 0
