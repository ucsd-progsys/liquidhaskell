


module Meas () where

import Language.Haskell.Liquid.Prelude



prop1       = map choo [[True]] -- replace [[1]] with [[]] for UNSAT
choo (x:xs) = liquidAssertB False
-- choo []     = liquidAssertB False

-- import qualified Data.Map as M
-- import Data.List (foldl')

--keyvals :: [(Int, Int)]
--keyvals = [(1, 1), (2, 2), (3, 3)]
--
--group :: (Ord k) => [(k, v)] -> M.Map k [v]
--group = foldl' addKV  M.empty
--
--addKV m (k, v) = let boo = liquidAssertB False in M.insert k vs' m
--  where vs' = v : (M.findWithDefault [] k m)
--
--checkNN m = M.foldrWithKey reduceKV False m
--
--reduceKV _ _ acc = liquidAssertB False 
--
--prop = checkNN (group keyvals)
