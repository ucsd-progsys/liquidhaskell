
-- | This module contains the types for representing dependency
--   graphs between kvars and constraints.

{-# LANGUAGE ImplicitParams        #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Fixpoint.Graph.Types (

  -- * Graphs
    CVertex (..)
  , CEdge
  , KVGraph (..)

  -- * Components
  , Comps
  , KVComps

  -- * Printing
  , writeGraph

  -- * Constraints
  , CId
  , CSucc
  , KVRead
  , DepEdge

  -- * Slice of relevant constraints
  , Slice (..)

  -- * Constraint Dependency Graphs
  , CGraph (..)

  -- * Alias for Constraint Maps
  , CMap
  , lookupCMap

  -- * Ranks
  , Rank (..)

  -- * Constraint Dependencies
  , CDeps (..)

  -- * Solver Info
  , SolverInfo (..)
  )
  where

import           GHC.Generics              (Generic)
import           Data.Hashable
import           Text.PrettyPrint.HughesPJ

import           Language.Fixpoint.Misc         -- hiding (group)
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Refinements -- Constraints

-- import           Language.Fixpoint.Misc (safeLookup)
import qualified Language.Fixpoint.Types   as F
import qualified Data.HashMap.Strict       as M
import GHC.Stack
--------------------------------------------------------------------------------

data CVertex = KVar  !KVar    -- ^ real kvar vertex
             | DKVar !KVar    -- ^ dummy to ensure each kvar has a successor
             | Cstr  !Integer -- ^ constraint-id which creates a dependency
               deriving (Eq, Ord, Show, Generic)

instance PPrint CVertex where
  pprintTidy _ (KVar k)  = doubleQuotes $ pprint $ kv k
  pprintTidy _ (Cstr i)  = text "id_" <> pprint i
  pprintTidy _ (DKVar k) = pprint k   <> text "*"


instance Hashable CVertex

data KVGraph    = KVGraph { kvgEdges :: [(CVertex, CVertex, [CVertex])] }
type CEdge      = (CVertex, CVertex)
type Comps a    = [[a]]
type KVComps    = Comps CVertex

--------------------------------------------------------------------------------
writeGraph :: FilePath -> KVGraph -> IO ()
--------------------------------------------------------------------------------
writeGraph f = writeFile f . render . ppGraph

ppGraph :: KVGraph -> Doc
ppGraph (KVGraph g) = ppEdges [ (v, v') | (v,_,vs) <- g, v' <- vs]

ppEdges :: [CEdge] -> Doc
ppEdges             = vcat . wrap ["digraph Deps {"] ["}"]
                           . map ppE
                           . filter (not . isJunkEdge)
  where
    ppE (v, v')     = pprint v <+> "->" <+> pprint v'

isJunkEdge :: CEdge -> Bool
isJunkEdge (DKVar _, _)     = True
isJunkEdge (_, DKVar _)     = True
isJunkEdge (Cstr _, Cstr _) = True
isJunkEdge _                = False



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
                     , gRanks :: !(CMap Int)
                     , gSucc  :: !CSucc
                     , gSccs  :: !Int
                     }

---------------------------------------------------------------------------
-- | CMap API -------------------------------------------------------------
---------------------------------------------------------------------------

lookupCMap :: (?callStack :: CallStack) => CMap a -> CId -> a
lookupCMap rm i = safeLookup err i rm
  where
    err      = "lookupCMap: cannot find info for " ++ show i

--------------------------------------------------------------------------------
-- | Constraint Dependencies ---------------------------------------------------
--------------------------------------------------------------------------------

data CDeps = CDs { cSucc   :: !CSucc
                 , cRank   :: !(CMap Rank)
                 , cNumScc :: !Int
                 }


-- | Ranks ---------------------------------------------------------------------

data Rank = Rank { rScc  :: !Int    -- ^ SCC number with ALL dependencies
                 , rIcc  :: !Int    -- ^ SCC number without CUT dependencies
                 , rTag  :: !F.Tag  -- ^ The constraint's Tag
                 } deriving (Eq, Show)

instance PPrint Rank where
  pprintTidy _ = text . show

--------------------------------------------------------------------------------
-- | `SolverInfo` contains all the stuff needed to produce a result, and is the
--   the essential ingredient of the state needed by solve_
--------------------------------------------------------------------------------
data SolverInfo a = SI
  { siSol   :: !F.Solution
  , siQuery :: !(F.SInfo a)
  , siDeps  :: !CDeps
  }
