module Language.Fixpoint.Solver.Types where

import qualified Data.HashMap.Strict     as M
import qualified Language.Fixpoint.Types as F


type Result a = (F.FixResult (F.SubC a), M.HashMap F.Symbol F.Pred)

type Solution = () -- TODOSolution

foo :: Int -> Int
foo x = x + 1

    
