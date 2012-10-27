{-# LANGUAGE TupleSections #-}
-- | This module contains the code for generating "tags" for constraints
-- based on their source, i.e. the top-level binders under which the
-- constraint was generated. These tags are used by fixpoint in
-- Language.Haskell.Liquid.FixInterface to prioritize constraints by the
-- source function.

module Language.Haskell.Liquid.CTags (
    -- * Type for constraint tags
    TagKey, TagEnv
 
    -- * Default tag value
  , defaultTag
   
    -- * Constructing @TagEnv@
  , makeTagEnv
  
    -- * Accessing @TagEnv@
  , getTag, memTagEnv

) where

import Var
import CoreSyn

import qualified Data.List  as L
import qualified Data.Set   as S
import qualified Data.Map   as M
import qualified Data.Graph as G

import Language.Haskell.Liquid.Misc         (mapSnd, traceShow)
import Language.Haskell.Liquid.Fixpoint     (Tag)
import Language.Haskell.Liquid.GhcInterface (freeVars)

-- | The @TagKey@ is the top-level binder, and @Tag@ is a singleton Int list

type TagKey = Var
type TagEnv = M.Map TagKey Tag

-- TODO: use the "callgraph" SCC to do this numbering.

defaultTag :: Tag
defaultTag = [0]

memTagEnv :: TagKey -> TagEnv -> Bool
memTagEnv = M.member

makeTagEnv :: [CoreBind] -> TagEnv 
makeTagEnv = M.map (:[]) . callGraphRanks . makeCallGraph 

-- makeTagEnv = M.fromList . (`zip` (map (:[]) [1..])). L.sort . map fst . concatMap bindEqns

getTag :: TagKey -> TagEnv -> Tag
getTag = M.findWithDefault defaultTag

------------------------------------------------------------------------------------------------------

type CallGraph = [(Var, [Var])] -- caller-callee pairs



callGraphRanks :: CallGraph -> M.Map Var Int
callGraphRanks cg = traceShow ("CallGraph Ranks: " ++ show cg) $ callGraphRanks' cg

callGraphRanks'  = M.fromList . concat . index . mkScc
  where mkScc cg = G.stronglyConnComp [(u, u, vs) | (u, vs) <- cg]
        index    = zipWith (\i -> map (, i) . G.flattenSCC) [1..] 

makeCallGraph :: [CoreBind] -> CallGraph
makeCallGraph cbs = mapSnd calls `fmap` xes 
  where xes       = concatMap bindEqns cbs
        xs        = S.fromList $ map fst xes
        calls     = filter (`S.member` xs) . freeVars S.empty

bindEqns (NonRec x e) = [(x, e)]
bindEqns (Rec xes)    = xes 


