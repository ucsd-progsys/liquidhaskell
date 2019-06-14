module Language.Haskell.Liquid.Synthesis where

import qualified Data.Graph as G
import           Data.Hashable
import           Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import qualified Data.HashMap.Strict as M
import           Prelude

import qualified Language.Fixpoint.Types                    as F
import           Language.Haskell.Liquid.Types
import           Util (fstOf3)
import           Var


-- | Returns a list of strongly connected components of hole dependencies. 
-- Results are returned in reverse topological order.
holeDependencySSC :: M.HashMap Var (HoleInfo i SpecType) -> [G.SCC (Var, HoleInfo i SpecType)]
holeDependencySSC holeMap = 
    -- let seen = Set.empty in
    let holes = M.toList holeMap in

    -- Find hole's dependencies.
    let deps = map (zipL (Set.toList . findDependencies)) holes in

    -- Build graph.
    let (graph, nodeFromVertex, _vertexFromKey) = G.graphFromEdges deps in

    -- Get strongly connected components, reverse topologically sorted.
    G.stronglyConnComp deps


    -- -- Sort by partial ordering.
    -- let vertices = reverse $ G.topSort graph in -- JP: Use revTopSort if they merge.

    -- Just $ map (fstOf3 . nodeFromVertex) vertices


    -- let deps = map (zipL $ (fmap Set.toList . findDependencies seen)) holes in

    -- -- Return Nothing if cycle found.
    -- case sequence deps of
    --     Nothing ->
    --         Nothing

    --     Just deps ->

    --         -- Build graph.
    --         let (graph, nodeFromVertex, _vertexFromKey) = G.graphFromEdges deps in

    --         -- Sort by partial ordering.
    --         let vertices = reverse $ G.topSort graph in -- JP: Use revTopSort if they merge.

    --         Just $ map (fstOf3 . nodeFromVertex) vertices


    where
        zipL :: ((k,v) -> [k]) -> (k,v) -> ((k,v), k, [k])
        zipL f x@(k,_) = (\y -> (x,k,y)) $ f x

        -- Find all holes that this hole is dependent on.
        findDependencies :: (Var, HoleInfo i SpecType) -> HashSet Var
        findDependencies (_, hi) = 
            -- JP: Do we need to consider reft?

            -- Union vars in environment.
            let REnv{..} = henv hi in
            let envVars = M.keysSet reLocal `Set.union` M.keysSet reGlobal in

            -- Only return holes.
            Set.filter ((`Set.member` envVars) . F.symbol) $ M.keysSet holeMap

        -- zipL :: ((k,v) -> Maybe [k]) -> (k,v) -> Maybe ((k,v), k, [k])
        -- zipL f x@(k,_) = (\y -> (x,k,y)) <$> f x

        -- findDependencies :: HashSet Var -> (Var, HoleInfo SpecType) -> Maybe (HashSet Var)
        -- findDependencies seen (v, _) | v `Set.member` seen = 
        --     if v `M.member` holeMap then 
        --         -- If we've seen this hole before, there's a cycle.
        --         Nothing
        --     else
        --         -- Otherwise, we're done.
        --         Just mempty -- JP: Should we return Nothing here too?
        --         
        -- findDependencies seen' (v, hi) =
        --     -- Add v to seen.
        --     let seen = Set.insert v seen' in

        --     -- Lookup refinement type of v in environment.
        --     let reftM = lookupAREnv v $ henv hi in
        --     
        --     case reftM of
        --         Nothing ->
        --             -- JP: What do we do if it's not in the environment? Is it an error? Or it has no dependencies?
        --             error "JP: findDependencies - what do we do here?"
        --         Just reft ->

        --             -- Get set of variables in reft of v.
        --             let vars' = reftToVars reft in

        --             -- Remove v from set of variables.
        --             -- JP: Should it be an error if v `member` vars'?
        --             let vars = Set.delete v vars' in

        --             -- Recursively find dependencies of set of variables.
        --             let deps' = sequence $ map (\v -> findDependencies seen (v, hi)) $ Set.toList vars in -- JP: Reuse `hi`?

        --             -- Check if there are any cycles in dependencies.
        --             -- JP: Do we need to do this here? We do it earlier already?
        --             
        --             -- Union all dependencies.
        --             let deps = (Set.unions . (vars:)) <$> (deps') in

        --             -- Return all dependencies that are holes.
        --             Set.filter (`M.member` holeMap) <$> deps
        --             

        -- -- JP: Does a function like this already exist?
        -- -- What's the right way to convert Var to Symbol?
        -- lookupAREnv :: Var -> AREnv t -> Maybe t
        -- lookupAREnv v REnv{..} = 
        --     let s = F.symbol v in

        --     -- Lookup local first.
        --     case M.lookup s reLocal of
        --         Just r -> 
        --             Just r
        --         Nothing -> 
        --             -- Lookup global next.
        --             M.lookup s reGlobal

        -- reftToVars :: SpecType -> HashSet Var
        -- reftToVars (RVar v t)                 = error "TODO"
        -- reftToVars (RFun bind rin rout reft)  = error "TODO"
        -- reftToVars (RImpF bind rin rout reft) = error "TODO"
        -- reftToVars (RAllT bind ty)            = error "TODO"
        -- reftToVars (RAllP bind ty)            = error "TODO"
        -- reftToVars (RApp con args pargs reft) = error "TODO"
        -- reftToVars (RAllE bind all ty)        = error "TODO"
        -- reftToVars (REx bind exarg ty)        = error "TODO"
        -- reftToVars (RExprArg lExpr)           = error "TODO"
        -- reftToVars (RAppTy arg res reft)      = error "TODO"
        -- reftToVars (RRTy env ref ob ty)       = error "TODO"
        -- reftToVars (RHole r)                  = error "TODO"
                        
