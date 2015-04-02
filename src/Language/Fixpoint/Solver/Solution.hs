module Language.Fixpoint.Solver.Solution
        ( -- * Solutions and Results
          Solution
        , Result

          -- * Initial Solution
        , init

          -- * Convert a Solution to a Result
        , result
        )
where


import           Prelude hiding (init)
import qualified Data.List               as L
import qualified Data.HashMap.Strict     as M
import qualified Language.Fixpoint.Types as F
import           Language.Fixpoint.Config
import           Language.Fixpoint.Solver.Monad

---------------------------------------------------------------------------
-- | Types ----------------------------------------------------------------
---------------------------------------------------------------------------

type Result a = (F.FixResult (F.SubC a), M.HashMap F.Symbol F.Pred)

type Solution = Sol KBind

type Sol a    = M.HashMap F.Symbol a

data KBind    = Bot | Asgn [EQual]

---------------------------------------------------------------------------
-- | Expanded or Instantiated Qualifier -----------------------------------
---------------------------------------------------------------------------

data EQual = EQ { eqQual :: !F.Qualifier
                , eqPred :: !F.Pred
                , eqArgs :: ![F.Expr]
                }
               deriving (Eq, Ord, Show)

{-@ data EQual = EQ { eqQual :: F.Qualifier
                    , eqPred :: F.Pred
                    , eqArgs :: {v: [F.Expr] | len v = len (q_params eqQual)}
                    }
  @-}

---------------------------------------------------------------------------
-- | Create Initial Solution from Qualifiers and WF constraints
---------------------------------------------------------------------------
init :: Config -> F.FInfo a -> Solution
---------------------------------------------------------------------------
init _ fi = L.foldl' (refine qs) s0 ws
  where
    s0    = M.empty
    qs    = F.quals fi
    ws    = F.ws    fi


refine :: F.FInfo a -> [F.Qualifier] -> Solution -> F.WfC a -> Solution
refine fi qs s w   = refineK env qs s k
  where
    env            = wfEnv fi w
    k              = wfKvar w

refineK env qs s k
  | Just eqs <- M.lookup k s = error "TODO"
  | otherwise                = error "TODO"

wfKvar :: F.WfC a -> F.Symbol
wfKvar = error "TODO"

wfEnv :: F.FInfo a -> F.WfC a -> F.SEnv F.SortedReft
wfEnv = undefined

okInst :: F.SEnv F.SortedReft -> F.SortedReft -> Bool
okInst = error "TODO:using checkSortedReftFull"

---------------------------------------------------------------------------
-- | Convert Solution into Result
---------------------------------------------------------------------------
result :: F.FInfo a -> Solution -> SolveM (Result a)
---------------------------------------------------------------------------
result = error "TODO"
