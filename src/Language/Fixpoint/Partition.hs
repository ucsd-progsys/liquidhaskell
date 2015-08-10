{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveGeneric #-}

-- | This module implements functions that print out
--   statistics about the constraints.

module Language.Fixpoint.Partition (partition, partition', partitionN) where

import           Control.Monad (forM_)
import           GHC.Generics                   (Generic)
import           Language.Fixpoint.Misc         hiding (group)-- (fst3, safeLookup, mlookup, groupList)
import           Language.Fixpoint.Solver.Deps
import           Language.Fixpoint.Files
import           Language.Fixpoint.Config
import           Language.Fixpoint.PrettyPrint
import qualified Language.Fixpoint.Visitor      as V
import qualified Language.Fixpoint.Types        as F
import qualified Data.HashMap.Strict            as M
import qualified Data.Graph                     as G
import qualified Data.Tree                      as T
import           Data.Hashable
import           Text.PrettyPrint.HughesPJ
import           Debug.Trace
import           Data.List (sortBy)

#if __GLASGOW_HASKELL__ < 710
import           Data.Monoid (mempty)
import           System.Console.CmdArgs.Verbosity (whenLoud)
import           Control.Applicative              ((<$>))
import           Control.Arrow ((&&&))
import           Data.List (sort,group)
import           Data.Maybe (mapMaybe)
import           System.FilePath -- (dropExtension)
#endif

partition :: (F.Fixpoint a) => Config -> F.FInfo a -> IO (F.Result a)
partition cfg fi
  = do dumpPartitions cfg fis
       dumpEdges      cfg es
       -- whenLoud $ putStrLn $ render $ ppGraph es
       return mempty
    where
       (es, fis) = partition' Nothing fi

partition' :: Maybe Int -> F.FInfo a -> (KVGraph, [F.FInfo a])
partition' mn fi  = case mn of
   Nothing -> (g, partitionByConstraints fi css)
   (Just n) -> (g, partitionN n fi $ partitionByConstraints' fi css)
  where
    es                 = kvEdges   fi
    g                  = kvGraph   es
    css                = decompose g


partitionN :: Int -> F.FInfo a -> [F.CPart a] -> [F.FInfo a]
partitionN n fi cp = map (cpartToFinfo fi) $ toNParts sortedParts
   where
      toNParts p
         | isDone p = p
         | otherwise = toNParts $ insertInPlace firstTwo theRest
            where (firstTwo, theRest) = unionFirstTwo p
      isDone fi' = length fi' <= n
      sortedParts = sortBy sortPredicate cp
      unionFirstTwo (a:b:xs) = (a `mappend` b, xs)
      sortPredicate lhs rhs
         | M.size (F.pcs lhs) < M.size (F.pcs rhs) = LT
         | M.size (F.pcs lhs) > M.size (F.pcs rhs) = GT
         | otherwise = EQ
      insertInPlace a [] = [a]
      insertInPlace a (x:xs) = if sortPredicate a x == LT
                               then x : insertInPlace a xs
                               else x:a:xs

cpartToFinfo :: F.FInfo a -> F.CPart a -> F.FInfo a
cpartToFinfo fi p = fi { F.cm = F.pcs p
                       , F.ws = F.pws p
                       , F.fileName = F.cFileName p
                       }

-------------------------------------------------------------------------------------
dumpPartitions :: (F.Fixpoint a) => Config -> [F.FInfo a] -> IO ()
-------------------------------------------------------------------------------------
dumpPartitions cfg fis =
  forM_ fis $ \fi ->
    writeFile (F.fileName fi) (render $ F.toFixpoint cfg fi)

partFile :: F.FInfo a -> Int -> FilePath
partFile fi j = {- trace ("partFile: " ++ fjq) -} fjq
  where
    fjq = extFileName (Part j) (F.fileName fi)

-------------------------------------------------------------------------------------
dumpEdges :: Config -> KVGraph -> IO ()
-------------------------------------------------------------------------------------
dumpEdges cfg = writeFile f . render . ppGraph
  where
    f         = extFileName Dot (inFile cfg)

ppGraph :: KVGraph -> Doc
ppGraph g = ppEdges [ (v, v') | (v,_,vs) <- g, v' <- vs]

ppEdges :: [CEdge] -> Doc
ppEdges es = vcat [pprint v <+> text "-->" <+> pprint v' | (v, v') <- es]

-------------------------------------------------------------------------------------
partitionByConstraints :: F.FInfo a -> KVComps -> [F.FInfo a]
-------------------------------------------------------------------------------------
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
       , F.ws =              M.lookupDefault [] j iwM
       , F.fileName = partFile fi j
       }

partitionByConstraints' :: F.FInfo a -> KVComps -> [F.CPart a]
partitionByConstraints' fi kvss = mkPartition' fi icM iwM <$> js
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

mkPartition' fi icM iwM j
  = F.CPart { F.pcs = M.fromList $ M.lookupDefault [] j icM
            , F.pws = M.lookupDefault [] j iwM
            , F.cFileName = partFile fi j
            }

wfGroup gk w = case sortNub [gk k | k <- wfKvars w ] of
                 [i] -> i
                 _   -> errorstar $ "PARTITION: wfGroup" ++ show (F.wid w)

wfKvars :: F.WfC a -> [F.KVar]
wfKvars = V.kvars . F.sr_reft . F.wrft

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

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
decompose :: KVGraph -> KVComps
-------------------------------------------------------------------------------------
decompose kg = {- tracepp "flattened" $ -} map (fst3 . f) <$> vss
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
    selfes = [(Cstr i, Cstr i) | c <- cs, let i = F.subcId c] ++
             [(KVar k, KVar k) | k <- fiKVars fi]

fiKVars :: F.FInfo a -> [F.KVar]
fiKVars fi = sortNub $ concatMap (wfKvars) (F.ws fi)


subcEdges :: F.BindEnv -> F.SubC a -> [CEdge]
subcEdges bs c =  [(KVar k, Cstr i ) | k  <- lhsKVars bs c]
               ++ [(Cstr i, KVar k') | k' <- rhsKVars c ]
  where
    i          = F.subcId c
