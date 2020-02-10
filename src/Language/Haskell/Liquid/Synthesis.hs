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


    where
        zipL :: ((k,v) -> [k]) -> (k,v) -> ((k,v), k, [k])
        zipL f x@(k,_) = (\y -> (x,k,y)) $ f x

        -- Find all holes that this hole is dependent on.
        findDependencies :: (Var, HoleInfo i SpecType) -> HashSet Var
        findDependencies (v, hi) = 

            -- Union vars in environment.
            let REnv{..} = henv hi in
            let envVars' = M.keysSet reLocal `Set.union` M.keysSet reGlobal in

            -- Remove v from set of variables.
            -- JP: Should it be an error if v `member` vars'?
            let envVars = Set.delete (F.symbol v) envVars' in

            -- Only return holes.
            Set.filter ((`Set.member` envVars) . F.symbol) $ M.keysSet holeMap
