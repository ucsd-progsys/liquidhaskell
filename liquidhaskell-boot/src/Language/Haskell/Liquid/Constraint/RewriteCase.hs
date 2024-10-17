module Language.Haskell.Liquid.Constraint.RewriteCase 
    (getCaseRewrites) 
    where

import           Language.Fixpoint.Types
import qualified Language.Fixpoint.Misc as M
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.RType

import           Data.Maybe
import           Data.Tuple

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S

getCaseRewrites :: CGEnv -> SpecType -> LocalRewrites
getCaseRewrites γ spec =
    let Reft (_, refinement) = ur_reft $ rt_reft spec
        -- Names of constustors both type constructors and data constructors
        ctors   = toSet $ seBinds  $ constEnv γ
        -- All the global names (top level functions, types, etc...)
        globals = toSet $ reGlobal $ renv     γ
    in unloop
       $ concatMap (uncurry $ unify ctors globals)
       $ groupUnifiableEqualities 
       $ getEqualities refinement
    where toSet = S.fromList . M.keys

-- | Generates substitutions for non-global variables that make @e1@ and @e2@
-- equal.
--
-- If @v@ is not global, and @C@ is a data constructor
--
--  * @v@ and @e2@ produces @(v, e2)@
--  * @e1@ and @v@ produces @(e1, v)@
--  * @C a₁ ... aₙ@ and @C b₁ ... bₙ@ produces the substitutions from unifying
--    @(a₁, b₁), ..., (aₙ, bₙ)@
--
-- If any unification fails, the substitutions from the unifications that
-- succeed are still produced.
--
unify :: S.HashSet Symbol -> S.HashSet Symbol -> Expr -> Expr -> [(Symbol, Expr)]
unify ctors globals = go
    where
        go e1 e2 | e1 == e2 = []
        -- NOTE: We don't need to check for ECst because the expressions arent
        -- elaborated
        go (EVar s1) e2 | isLocal s1 = [(s1, e2)]
        go e1 (EVar s2) | isLocal s2 = [(s2, e1)]
        -- TODO: Tecnically we could also unify under lambdas but you have to be
        -- carefull about alpha equivalence idk if the effort is worth it.
        go e1 e2 
            -- Performing the unification under constructor is safe because 
            -- C a₁ ... aₙ = C b₁ ... bₙ ⟺ ∀ n . a₁ = bₙ
            | (EVar name1 , args1) <- splitEApp e2
            , (EVar name2 , args2) <- splitEApp e1
            , name1 == name2
            , isCtor name1
            , length args1 == length args2
            = concat $ zipWith go args1 args2
        go _ _ = []

        isCtor  name = name `S.member` ctors
        isLocal name = not (name `S.member` globals 
                           || name `S.member` ctors
                           || isPrefixOfSym anfPrefix name)


-- | Given a list of equalities this function produces the equalities that
-- result from applying transitivity exactly once through terms that are not
-- unifiable. For instance, if we have @[e1=e2, e2=e3, e1=e4]@ this function
-- will produce @[e1=e3, e2=e4]@.
--
-- Some equalities are not produced if more than two equalities refer to the
-- same expression. For instance, @[e1=e2, e1=e3, e1=e4]@, becase @e1@ appears
-- three times, the equality @e3=e4@ won't be produced. This is an heuristic
-- to avoid producing equalities that can later produce redundant rewrites.
groupUnifiableEqualities :: [(Expr, Expr)] -> [(Expr, Expr)]
groupUnifiableEqualities = concatMap mkEqs . grouping
  where
    mkEqs (e1: es) = [ (e1, e) | e <- es ]
    mkEqs _        = []

    grouping eqs = fmap snd $ M.groupList $ eqs ++ fmap swap eqs

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

-- We can think of the map as a directed graph where every symbol is a vertex and
-- there is an edge v₁ → v₂ if v₂ is free in the expression that v₁ is rewritten to.
-- To guarantee that the set of rewrite rules is terminating, we ensure that there
-- aren't any cycles in the graph.

-- | Drops rewrites that would cause an infinite loop. The procedure is order
-- biased as rewrites earlier in the list take precedence.
unloop :: [(Symbol, Expr)] -> LocalRewrites
unloop = LocalRewrites . toRewrites . foldl' doInsert empty 
    where doInsert ar (s, e) = ar `fromMaybe` insert ar s e 

-- | Get the "raw" list of rewrites
toRewrites :: AcyclicRewrites -> M.HashMap Symbol Expr
toRewrites (AR m) = m

-- | @existsPth g s1 s2@ yields @True@ checks if there is a path from @s1@ to @s2@
-- in @g@. Time is @O(Σ(e ∈ m) |exprSymbolSet e|)@, or said otherwise, it is @O(m)@
-- where @m@ is the number of edges.
existsPath :: AcyclicRewrites -> Symbol -> Symbol -> Bool
existsPath (AR m) s1' s2 = go s1'
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
insert ar s e | not $ s `S.member` exprSymbolsSet e
              , not $ any (\s2 -> existsPath ar s2 s) $ S.toList $ exprSymbolsSet e
              -- There are two ways to break the DAG invariant
              -- 1. If the rewrite is closing a loop
              -- 2. If the rewrite by itself is a cycle
              = Just $ insertUnsafe ar s e
              | otherwise 
              = Nothing
    where insertUnsafe (AR m) s' e' = AR $ M.insert s' e' m
