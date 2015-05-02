-- | Validate and Transform Constraints to Ensure various Invariants -------------------------
--   1. Each binder must be unique

module Language.Fixpoint.Solver.Validate
       ( -- * Validate and Transform FInfo to enforce invariants
         validate
         -- * Sorts for each Symbol
       , symBinds
       )
       where

import           Language.Fixpoint.Config
import           Language.Fixpoint.PrettyPrint
import qualified Language.Fixpoint.Misc   as Misc
import qualified Language.Fixpoint.Types  as F
import qualified Language.Fixpoint.Errors as E
import qualified Data.HashMap.Strict      as M
import qualified Data.List as L
-- import           Control.Monad (filterM)
-- import           Control.Applicative ((<$>))
-- import           Debug.Trace (trace)
import           Text.Printf

validate :: Config -> F.FInfo a -> Either E.Error (F.FInfo a)
validate _ = checkUnique . renameVV

---------------------------------------------------------------------------
-- | Check whether each binder appears with a UNIQUE SORT in the BindEnv
---------------------------------------------------------------------------
checkUnique :: F.FInfo a -> Either E.Error (F.FInfo a)
---------------------------------------------------------------------------
checkUnique fi = case duplicates $ F.bs fi of
                  [] -> Right fi
                  ds -> Left $ dupBindErrors ds

duplicates :: F.BindEnv -> [SymBinds]
duplicates = filter ((1 <) . length . snd) . symBinds

dupBindErrors :: [SymBinds] -> E.Error
dupBindErrors = foldr1 E.catError . map dupBindError

dupBindError :: SymBinds -> E.Error
dupBindError (x, y) = E.err E.dummySpan
                    $ printf "Multiple sorts for %s : %s \n" (showpp x) (showpp y)

---------------------------------------------------------------------------
symBinds  :: F.BindEnv -> [SymBinds]
---------------------------------------------------------------------------
symBinds  = M.toList
          . M.map Misc.groupList
          . Misc.group
          . binders

type SymBinds = (F.Symbol, [(F.Sort, [F.BindId])])

binders :: F.BindEnv -> [(F.Symbol, (F.Sort, F.BindId))]
binders be = [(x, (F.sr_sort t, i)) | (i, x, t) <- F.bindEnvToList be]

---------------------------------------------------------------------------
-- | Alpha Rename bindings to ensure each var appears in unique binder
---------------------------------------------------------------------------
renameVV :: F.FInfo a -> F.FInfo a
---------------------------------------------------------------------------
renameVV fi = fi {F.bs = be'}
  where
    vts     = map subcVV $ M.elems $ F.cm fi
    be'     = L.foldl' addVV be vts
    be      = F.bs fi

addVV :: F.BindEnv -> (F.Symbol, F.SortedReft) -> F.BindEnv
addVV b (x, t) = snd $ F.insertBindEnv x t b

subcVV :: F.SubC a -> (F.Symbol, F.SortedReft)
subcVV c = (x, sr)
  where
    sr   = F.slhs c
    x    = F.reftBind $ F.sr_reft sr
