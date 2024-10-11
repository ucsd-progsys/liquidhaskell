module Language.Haskell.Liquid.Constraint.RewriteCase 
    (getCaseRewrites) 
    where

import           Language.Fixpoint.Types
import qualified Language.Fixpoint.Misc as M
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Types.Types

import           Data.Maybe
import           Control.Monad

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S

getCaseRewrites :: CGEnv -> SpecType -> [(Symbol, Expr)]
getCaseRewrites γ spec =
    let Reft (_, refinement) = ur_reft $ rt_reft spec
        -- Names of constustors both type constructors and data constructors
        ctors   = toSet $ seBinds  $ constEnv γ
        -- All the global names (top level functions, types, etc...)
        globals = toSet $ reGlobal $ renv     γ
    in unloop
       $ concat
       $ mapMaybe (uncurry $ unify ctors globals)
       $ groupUnifiableEqualities 
       $ getEqualities refinement
    where toSet = S.fromList . M.keys

unify :: S.HashSet Symbol -> S.HashSet Symbol -> Expr -> Expr -> Maybe [(Symbol, Expr)]
unify ctors globals = go
    where
        go e1 e2 | e1 == e2 = Just []
        -- NOTE: We don't need to check for ECst because the expressions arent
        -- elaborated
        go (EVar s1) e2 | isLocal s1 = Just [(s1, e2)]
        go e1 (EVar s2) | isLocal s2 = Just [(s2, e1)]
        -- TODO: Tecnically we could also unify under lambdas but you have to be
        -- carefull about alpha equivalence idk if the effort is worth it.
        go e1 e2 = do
            -- Performing the unification under constructor is safe because 
            -- C a₁ ... aₙ = C b₁ ... bₙ ⟺ ∀ n . a₁ = bₙ
            let EVar name1 : args1 = flatten e1
            let EVar name2 : args2 = flatten e2
            guard $ name1 == name2
            guard $ isCtor name1
            guard $ length args1 == length args2
            concat <$> zipWithM go args1 args2

        isCtor  name = name `S.member` ctors
        isLocal name = not (name `S.member` globals 
                           || name `S.member` ctors
                           || isPrefixOfSym anfPrefix name)

flatten :: Expr -> [Expr]
flatten (EApp f e) = flatten f ++ [e]
flatten e = [e]

groupUnifiableEqualities :: [(Expr, Expr)] -> [(Expr, Expr)]
groupUnifiableEqualities = mapMaybe (keep2 . snd) . M.groupList 
    where -- We perform only 2-way unification
          keep2 [e1, e2] = Just (e1, e2)
          keep2 _        = Nothing

getEqualities :: Expr -> [(Expr, Expr)]
getEqualities (PAtom Eq e1 e2) = [(e1, e2)]
getEqualities (PAnd eqs)       = concatMap getEqualities eqs
getEqualities _                = []


-- +-----------------------------------------------------+
-- | AcyclicRewrites: collection of rewrites that cannot |
-- | cause an infinite loop                              |
-- +-----------------------------------------------------+
-- This could be extracted as a separate module

-- | A collection of rewrites that cannot cause an infinite loop
newtype AcyclicRewrites = AR (M.HashMap Symbol Expr)

-- We can think of the map a directed graph where every symbol is a vertex and
-- there is an edge v₁ → v₂ if in the expression that v₁ is rewritten to v₂ is a
-- free variable.  To guarantee that there arent any infinite loops in the
-- rewrite procedure that will be executed by PLE, we need to esnure that there
-- aren't any cyclic rewrites, this is ensured by adding the invariant to our
-- graph of beeing a DAG.

-- | Takes a list of rewrites and returns a list of rewrites and filters out any
-- rewrites that would cause an infinite loop, the procedure is order biased as
-- rewrites earlier in the list take precedence.
unloop :: [(Symbol, Expr)] -> [(Symbol, Expr)]
unloop = toRewrites . foldl' doInsert empty 
    where doInsert ar (s, e) = ar `fromMaybe` insert ar s e 

-- | Get the "raw" list of rewrites
toRewrites :: AcyclicRewrites -> [(Symbol, Expr)]
toRewrites (AR m) = M.toList m

-- | Checks if there is a path from s1 to s2 O(Σ(e ∈ m) |exprSymbolSet e|) [O(m)
-- where m is the number of edges]
existsPath :: AcyclicRewrites -> Symbol -> Symbol -> Bool
existsPath (AR m) s1 s2 = go s1
  where
    -- Since m is a DAG, we can use DFS to check if there is a path from s1 to
    -- s2 without worrying about infinite loops
    go s1 | s1 == s2 = True
    go s1 | Just e <- M.lookup s1 m
          = any go $ S.toList $ exprSymbolsSet e
    go _ = False

-- | Constructs an empty set of rewrites
empty :: AcyclicRewrites
empty = AR M.empty

-- | Inserts the rewrite if it wont't cause an infinite loop
insert :: AcyclicRewrites -> Symbol -> Expr -> Maybe AcyclicRewrites
insert ar s e | not $ any (existsPath ar s) $ S.toList $ exprSymbolsSet e
              , not $ s `S.member` exprSymbolsSet e
              -- There are two ways to break the DAG invariant
              -- 1. If the rewrite is closing a loop
              -- 2. If the rewrite by itself is a cycle
              = Just $ insertUnsafe ar s e
              | otherwise 
              = Nothing
    where insertUnsafe (AR m) s e = AR $ M.insert s e m
