
{-# LANGUAGE ImplicitParams        #-}

module Language.Fixpoint.Solver.Types where


import           Language.Fixpoint.Misc (safeLookup)
import qualified Language.Fixpoint.Types   as F
import qualified Data.HashMap.Strict       as M
import GHC.Stack
---------------------------------------------------------------------------
-- | Dramatis Personae
---------------------------------------------------------------------------

type CId     = Integer
type CSucc   = CId -> [CId]
type CMap a  = M.HashMap CId a
type KVRead  = M.HashMap F.KVar [CId]
type DepEdge = (CId, CId, [CId])

data Slice = Slice { slKVarCs :: [CId]     -- ^ CIds that transitively "reach" below
                   , slConcCs :: [CId]     -- ^ CIds with Concrete RHS
                   , slEdges  :: [DepEdge] -- ^ Dependencies between slKVarCs
                   } deriving (Eq, Show)

data CGraph = CGraph { gEdges :: [DepEdge]
                     , gRanks :: CMap Int
                     , gSucc  :: CSucc
                     , gSccs  :: Int
                     }

---------------------------------------------------------------------------
-- | CMap API -------------------------------------------------------------
---------------------------------------------------------------------------

lookupCMap :: (?callStack :: CallStack) => CMap a -> CId -> a
lookupCMap rm i = safeLookup err i rm
  where
    err      = "lookupCMap: cannot find info for " ++ show i
