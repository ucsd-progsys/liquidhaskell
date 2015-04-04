module Language.Fixpoint.Solver.Deps where


import qualified Language.Fixpoint.Types        as F

type KVar = F.Symbol

data Deps = Deps { depCuts    :: ![KVar]
                 , depNonCuts :: ![KVar]
                 }
            deriving (Eq, Ord, Show)

deps :: F.FInfo a -> Deps
deps = error "TODO"
