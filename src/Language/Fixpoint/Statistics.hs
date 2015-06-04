
{-# LANGUAGE DeriveGeneric #-}

-- | This module implements functions that print out
--   statistics about the constraints.


module Language.Fixpoint.Statistics (statistics) where

import           Control.Applicative                   ((<$>))
import           GHC.Generics                          (Generic)
import           Language.Fixpoint.Misc                (fst3, groupList)
import           Language.Fixpoint.Solver.Deps
import           Language.Fixpoint.Config       hiding (statistics)
import qualified Language.Fixpoint.Types        as F
import qualified Data.HashMap.Strict            as M
import qualified Data.Graph                     as G
import qualified Data.Tree                      as T
import           Data.Hashable
import           Data.Maybe (mapMaybe)

statistics :: Config -> F.FInfo a -> IO ()
statistics _ fi = putStrLn $ "STATS: " ++ show info
  where
    css         = decompose fi
    sizes       = fromIntegral . length <$> css
    info        = stats sizes

stats :: [Float] -> Maybe Stats
stats [] = Nothing
stats ns = Just Stats {
    cSizes  = ns
  , cTotal  = sum     ns
  , cMean   = mean    ns
  , cStdev  = stdDev  ns
  , cMax    = maximum ns
  }

stdDev :: [Float] -> Float
stdDev xs   = sqrt (sum [(x - μ)^2 | x <- xs] / n)
  where
    μ       = mean   xs
    n       = fromIntegral $ length xs

mean :: [Float] -> Float
mean ns  = sum ns / fromIntegral (length ns)


data Stats = Stats { cSizes  :: [Float]
                   , cTotal  :: Float
                   , cMean   :: Float
                   , cStdev  :: Float
                   , cMax    :: Float
                   } deriving (Show)


data CVertex = KVar F.KVar
             | Cstr Integer
               deriving (Eq, Ord, Show, Generic)

instance Hashable CVertex

type CEdge    = (CVertex, CVertex)
type KVGraph  = [(CVertex, CVertex, [CVertex])]

type Comps a  = [[a]]
type KVComps  = Comps CVertex
type SubComps = Comps Integer

decompose :: F.FInfo a -> SubComps
decompose = subComps . partition . kvGraph

subComps :: KVComps -> SubComps
subComps = map $ mapMaybe cstr
  where
    cstr (Cstr i) = Just i
    cstr _        = Nothing

partition :: KVGraph -> KVComps
partition kg = map (fst3 . f) <$> vss
  where
    (g,f,_)  = G.graphFromEdges kg
    vss      = T.flatten <$> G.components g


kvGraph :: F.FInfo a -> KVGraph
kvGraph fi = [(v,v,vs) | (v, vs) <- groupList es]
  where
    es     = concatMap (subcEdges bs) cs
    bs     = F.bs fi
    cs     = M.elems (F.cm fi)



subcEdges :: F.BindEnv -> F.SubC a -> [CEdge]
subcEdges bs c =  [(KVar k, Cstr i ) | k  <- lhsKVars bs c]
               ++ [(Cstr i, KVar k') | k' <- rhsKVars c ]
  where
    i          = F.subcId c

