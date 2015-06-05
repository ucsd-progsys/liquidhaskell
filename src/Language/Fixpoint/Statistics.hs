
{-# LANGUAGE DeriveGeneric #-}

-- | This module implements functions that print out
--   statistics about the constraints.


module Language.Fixpoint.Statistics (statistics) where

import           Control.Arrow ((&&&))
import           Control.Applicative                   ((<$>))
import           GHC.Generics                          (Generic)
import           Language.Fixpoint.Misc                (applyNonNull, fst3, groupList)
import           Language.Fixpoint.Solver.Deps
import           Language.Fixpoint.Config       -- hiding (statistics)
import           Language.Fixpoint.PrettyPrint
import qualified Language.Fixpoint.Types        as F
import qualified Data.HashMap.Strict            as M
import qualified Data.Graph                     as G
import qualified Data.Tree                      as T
import           Data.Hashable
import           Data.List (sort,group)
import           Data.Maybe (mapMaybe)
import           Text.PrettyPrint.HughesPJ

statistics :: Config -> F.FInfo a -> IO ()
statistics _ fi = do putStrLn $ render   $ ppGraph es
                     putStrLn $ render   $ pprint info
                     error "DONE: statistics"
                     -- putStrLn $ "COMPS: " ++ show css
                     -- exitWith ExitSuccess
  where
    es          = kvEdges   fi
    g           = kvGraph   es
    css         = decompose g
    sizes       = fromIntegral . length <$> css
    info        = applyNonNull Nothing (Just . mkStats) sizes

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


decompose :: KVGraph -> SubComps
decompose = subComps . partition

subComps :: KVComps -> SubComps
subComps = map $ mapMaybe cstr
  where
    cstr (Cstr i) = Just i
    cstr _        = Nothing

partition :: KVGraph -> KVComps
partition kg = tracepp "flattened" $ map (fst3 . f) <$> vss
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
  , cMax    = max
  , cSpeed  = total / max
  }
  where
    max     = maximum ns
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


