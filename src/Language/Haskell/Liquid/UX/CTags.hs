-- | This module contains the code for generating "tags" for constraints
--   based on their source, i.e. the top-level binders under which the
--   constraint was generated. These tags are used by fixpoint to
--   prioritize constraints by the "source-level" function.

{-# LANGUAGE TupleSections #-}

module Language.Haskell.Liquid.UX.CTags (
    -- * Type for constraint tags
    TagKey, TagEnv

    -- * Default tag value
  , defaultTag

    -- * Constructing @TagEnv@
  , makeTagEnv

    -- * Accessing @TagEnv@
  , getTag
  , memTagEnv

) where

import Var
import CoreSyn
import Prelude hiding (error)

import qualified Data.HashSet           as S
import qualified Data.HashMap.Strict    as M
import qualified Data.Graph             as G

import Language.Fixpoint.Types          (Tag)
import Language.Haskell.Liquid.Types.Visitors (freeVars)
import Language.Haskell.Liquid.Types.PrettyPrint ()
import Language.Fixpoint.Misc     (mapSnd)

-- | The @TagKey@ is the top-level binder, and @Tag@ is a singleton Int list

type TagKey = Var
type TagEnv = M.HashMap TagKey Tag

-- TODO: use the "callgraph" SCC to do this numbering.

defaultTag :: Tag
defaultTag = [0]

memTagEnv :: TagKey -> TagEnv -> Bool
memTagEnv = M.member

makeTagEnv :: [CoreBind] -> TagEnv
makeTagEnv = {- tracepp "TAGENV" . -} M.map (:[]) . callGraphRanks . makeCallGraph

-- makeTagEnv = M.fromList . (`zip` (map (:[]) [1..])). L.sort . map fst . concatMap bindEqns

getTag :: TagKey -> TagEnv -> Tag
getTag = M.lookupDefault defaultTag

------------------------------------------------------------------------------------------------------

type CallGraph = [(Var, [Var])] -- caller-callee pairs

callGraphRanks :: CallGraph -> M.HashMap Var Int
-- callGraphRanks cg = traceShow ("CallGraph Ranks: " ++ show cg) $ callGraphRanks' cg

callGraphRanks  = M.fromList . concat . index . mkScc
  where mkScc cg = G.stronglyConnComp [(u, u, vs) | (u, vs) <- cg]
        index    = zipWith (\i -> map (, i) . G.flattenSCC) [1..]

makeCallGraph :: [CoreBind] -> CallGraph
makeCallGraph cbs = mapSnd calls `fmap` xes
  where xes       = concatMap bindEqns cbs
        xs        = S.fromList $ map fst xes
        calls     = filter (`S.member` xs) . freeVars S.empty

bindEqns :: Bind t -> [(t, Expr t)]
bindEqns (NonRec x e) = [(x, e)]
bindEqns (Rec xes)    = xes
