module Language.Haskell.Liquid.Synthesis where

import           Data.Hashable
import           Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import qualified Data.HashMap.Strict as M
import           Prelude

import           Language.Haskell.Liquid.Types
import           Var


-- JP: What if there are multiple holes in the expression?
-- 
-- synthesize :: Var -> SpecType -> Env -> [Expr]
-- synthesize _ _ _ = []

data Graph a = Graph {
      rootNodes :: HashSet a
    , graphEdges :: M.HashMap a (HashSet a)
    }

-- | Builds a dependency graph where an edge from hole a to hole b indicates hole b is dependent on hole a.
-- Root holes are not dependent on other holes.
-- Returns Nothing if a cycle is detected.
holeDependencyGraph :: M.HashMap Var (HoleInfo SpecType) -> Maybe (Graph Var)
holeDependencyGraph holeMap = 
    let seen = Set.empty in
    let holes = M.keys holeMap in

    -- Find hole's dependencies.
    let deps = map (zipL $ findDependencies seen) holes in

    -- Return Nothing if cycle found.
    case sequence deps of
        Nothing ->
            Nothing

        Just deps ->

            -- Invert edges.
            let edges = M.fromListWith mappend $ invert deps in

            -- Find root nodes.
            let roots = findRoots edges in

            -- Build graph.
            Just $ Graph roots edges


    where
        zipL :: (a -> Maybe [a]) -> a -> Maybe (a, [a])
        zipL f x = (\y -> (x,y)) <$> f x

        -- Find all holes that this hole is dependent on.
        findDependencies :: HashSet Var -> Var -> Maybe [Var]
        findDependencies seen v | v `Set.member` seen = 
            if v `M.member` holeMap then 
                -- If we've seen this hole before, there's a cycle.
                Nothing
            else
                -- Otherwise, we're done.
                Just []
                
        findDependencies seen' v =
            -- Add v to seen.
            let seen = Set.insert v seen' in

            -- Lookup refinement type of v in environment.
            -- Get set of variables in reft of v.
            -- Remove v from set of variables.
            -- Recursively find dependencies of set of variables.
            -- Check if there are any cycles in dependencies.
            -- Union all dependencies.
            -- Return all dependencies that are holes.
            
            error "TODO"

        -- Expand edges and reverse the direction.
        invert :: Hashable a => [(a,[a])] -> [(a,HashSet a)]
        invert = concatMap (\(a, bs) -> map (\b -> ( b, Set.singleton a)) bs)
        
        -- Find root nodes (Nodes that do not have edges pointed towards them).
        findRoots :: (Hashable a, Eq a) => M.HashMap a (HashSet a) -> HashSet a
        findRoots m =
            let holes = M.keysSet m in
            M.foldr (\towards acc -> Set.difference acc towards) holes m


        



