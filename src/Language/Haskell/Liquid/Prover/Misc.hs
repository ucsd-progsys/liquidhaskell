module Language.Haskell.Liquid.Prover.Misc where

import Data.List




-------------------------------------------------------------------------------
-----------------------   Playing with lists    -------------------------------
-------------------------------------------------------------------------------

-- | Powerset 
powerset = sortBy (\l1 l2 -> compare (length l1) (length l2)) . powerset'

powerset'       :: [a] -> [[a]]
powerset' []     = [[]]
powerset' (x:xs) = xss /\/ map (x:) xss
   where xss = powerset' xs

(/\/)        :: [a] -> [a] -> [a]
[]     /\/ ys = ys
(x:xs) /\/ ys = x : (ys /\/ xs)




-------------------------------------------------------------------------------
-----------------------   Playing with monads   -------------------------------
-------------------------------------------------------------------------------

findM :: (Monad m) => (a -> m Bool) -> [a] -> m (Maybe a)
findM _ []     = return Nothing 
findM p (x:xs) = do {r <- p x; if r then return (Just x) else findM p xs}


mapSnd f (x, y) = (x, f y)

second3 f (x, y, z) = (x, f y, z)
