
{-# LANGUAGE DeriveGeneric #-}

-- | This module implements functions that print out
--   statistics about the constraints.

module Language.Fixpoint.Partition (partition) where

import           System.Console.CmdArgs.Verbosity (whenLoud)
import           Control.Arrow ((&&&))
-- import           Control.Applicative                   ((<$>))
import           GHC.Generics                          (Generic)
import           Language.Fixpoint.Misc         hiding (group)-- (fst3, safeLookup, mlookup, groupList)
import           Language.Fixpoint.Solver.Deps
import           Language.Fixpoint.Config       -- hiding (statistics)
import           Language.Fixpoint.PrettyPrint
import qualified Language.Fixpoint.Visitor      as V
import qualified Language.Fixpoint.Types        as F
import qualified Data.HashMap.Strict            as M
import qualified Data.Graph                     as G
import qualified Data.Tree                      as T
import           Data.Hashable
import           Data.List (sort,group)
-- import           Data.Maybe (mapMaybe)
import           Text.PrettyPrint.HughesPJ

partition :: Config -> F.FInfo a -> IO [F.FInfo a]
partition _ fi = do whenLoud $ putStrLn $ render $ ppGraph es
                    return fis
  where
    fis        = partitionByConstraints fi css
    es         = kvEdges   fi
    g          = kvGraph   es
    css        = decompose g

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
partitionByConstraints :: F.FInfo a -> KVComps -> [F.FInfo a]
partitionByConstraints fi kvss = mkPartition fi icM iwM <$> js
  where
    js   = fst <$> jkvs                                -- groups
    gc   = groupFun cM                                 -- (i, ci) |-> j
    gk   = groupFun kM                                 -- k       |-> j

    iwM  = groupMap (wfGroup gk) (F.ws fi)             -- j |-> [w]
    icM  = groupMap (gc . fst)   (M.toList (F.cm fi))  -- j |-> [(i, ci)]

    jkvs = zip [1..] kvss
    kvI  = [ (x, j) | (j, kvs) <- jkvs, x <- kvs ]
    kM   = M.fromList [ (k, i) | (KVar k, i) <- kvI ]
    cM   = M.fromList [ (c, i) | (Cstr c, i) <- kvI ]

mkPartition fi icM iwM j
  = fi { F.cm = M.fromList $ M.lookupDefault [] j icM
       , F.ws =              M.lookupDefault [] j iwM }

wfGroup gk w = case sortNub [gk k | k <- wfKvars w ] of
                 [i] -> i
                 _   -> errorstar $ "PARTITION: wfGroup" ++ show (F.wid w)

wfKvars :: F.WfC a -> [F.KVar]
wfKvars = V.kvars . F.sr_reft . F.wrft

ppGraph :: [CEdge] -> Doc
ppGraph es = text "GRAPH:" <+> vcat [pprint v <+> text "-->" <+> pprint v' | (v, v') <- es]

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------

data CVertex = KVar F.KVar
             | Cstr Integer
               deriving (Eq, Ord, Show, Generic)

instance PPrint CVertex where
  pprint (KVar k) = pprint k
  pprint (Cstr i) = text "id:" <+> pprint i


instance Hashable CVertex

type CEdge    = (CVertex, CVertex)
type KVGraph  = [(CVertex, CVertex, [CVertex])]

type Comps a  = [[a]]
type KVComps  = Comps CVertex
type SubComps = Comps Integer

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------

{-
decompose :: KVGraph -> SubComps
decompose = subComps . partitionGraph

subComps :: KVComps -> SubComps
subComps = map $ mapMaybe cstr
  where
    cstr (Cstr i) = Just i
    cstr _        = Nothing
-}

decompose :: KVGraph -> KVComps
decompose = partitionGraph

partitionGraph :: KVGraph -> KVComps
partitionGraph kg = tracepp "flattened" $ map (fst3 . f) <$> vss
  where
    (g,f,_)  = G.graphFromEdges kg
    vss      = T.flatten <$> G.components g

kvGraph :: [CEdge] -> KVGraph
kvGraph es = [(v,v,vs) | (v, vs) <- groupList es ]

kvEdges :: F.FInfo a -> [CEdge]
kvEdges fi = selfes ++ concatMap (subcEdges bs) cs
  where
    bs     = F.bs fi
    cs     = M.elems (F.cm fi)
    selfes = [(Cstr i, Cstr i) | c <- cs, let i = F.subcId c]

subcEdges :: F.BindEnv -> F.SubC a -> [CEdge]
subcEdges bs c =  [(KVar k, Cstr i ) | k  <- lhsKVars bs c]
               ++ [(Cstr i, KVar k') | k' <- rhsKVars c ]
  where
    i          = F.subcId c

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------

data Stats = Stats { cSizes  :: [Float]
                   , cFreq   :: [(Float, Int)]
                   , cTotal  :: Float
                   , cMean   :: Float
                   , cMax    :: Float
                   , cSpeed  :: Float
                   } deriving (Show)

instance PPrint Stats where
  pprint s = vcat [ text "STAT: max/total = " <+> pprint (cMax   s) <+> text "/" <+> pprint (cTotal s)
                  , text "STAT: freqs     = " <+> pprint (cFreq  s)
                  , text "STAT: average   = " <+> pprint (cMean  s)
                  , text "STAT: speed     = " <+> pprint (cSpeed s)
                  ]

mkStats :: [Float] -> Stats
mkStats ns  = Stats {
    cSizes  = ns
  , cFreq   = frequency ns
  , cTotal  = total
  , cMean   = avg
  , cMax    = maxx
  , cSpeed  = total / maxx
  }
  where
    maxx    = maximum ns
    total   = sum  ns
    avg     = mean ns

frequency :: (Ord a) => [a] -> [(a, Int)]
frequency = map (head &&& length) . group . sort

stdDev :: [Float] -> Float
stdDev xs   = sqrt (sum [(x - μ)^2 | x <- xs] / n)
  where
    μ       = mean   xs
    n       = fromIntegral $ length xs

mean :: [Float] -> Float
mean ns  = sum ns / fromIntegral (length ns)
