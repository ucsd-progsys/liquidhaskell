-- | Validate and Transform Constraints to Ensure various Invariants -------------------------

module Language.Fixpoint.Solver.Validate (validate) where

import           Language.Fixpoint.Config
import           Language.Fixpoint.PrettyPrint
import qualified Language.Fixpoint.Types  as F
import qualified Language.Fixpoint.Errors as E

import           Control.Monad (filterM)
import           Control.Applicative ((<$>))
import qualified Data.HashMap.Strict  as M
import qualified Data.List as L
import           Debug.Trace (trace)


validate :: Config -> F.FInfo a -> Either E.Error (F.FInfo a)
validate _ = Right



---------------------------------------------------------------------------
-- | Alpha Rename bindings to ensure each var appears in unique binder
---------------------------------------------------------------------------
rename :: F.FInfo a -> F.FInfo a
---------------------------------------------------------------------------

-- TODO: Fix `rename` to enforce uniqueness, AND add bindings for VVs
rename fi = fi {F.bs = be'}
  where
    vts   = map subcVV $ M.elems $ F.cm fi
    be'   = L.foldl' addVV be vts
    be    = F.bs fi

addVV :: F.BindEnv -> (F.Symbol, F.SortedReft) -> F.BindEnv
addVV b (x, t) = snd $ F.insertBindEnv x t b

subcVV :: F.SubC a -> (F.Symbol, F.SortedReft)
subcVV c = (x, sr)
  where
    sr   = F.slhs c
    x    = F.reftBind $ F.sr_reft sr
