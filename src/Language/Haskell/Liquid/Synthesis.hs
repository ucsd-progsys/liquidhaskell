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


-- | Builds a dependency graph where an edge from hole a to hole b indicates hole b is dependent on hole a.
-- Root holes are not dependent on other holes.
-- Returns Nothing if a cycle is detected.
holeDependencyOrder :: M.HashMap Var (HoleInfo SpecType) -> Maybe [(Var, HoleInfo SpecType)]
holeDependencyOrder holeMap = 
    let seen = Set.empty in
    let holes = M.toList holeMap in

    -- Find hole's dependencies.
    let deps = map (zipL $ findDependencies seen) holes in

    -- Return Nothing if cycle found.
    case sequence deps of
        Nothing ->
            Nothing

        Just deps ->

            -- Build graph.
            let (graph, nodeFromVertex, _vertexFromKey) = G.graphFromEdges deps in

            -- Sort by partial ordering.
            let vertices = reverse $ G.topSort graph in -- JP: Use revTopSort if they merge.

            Just $ map (fstOf3 . nodeFromVertex) vertices


    where
        zipL :: ((k,v) -> Maybe [k]) -> (k,v) -> Maybe ((k,v), k, [k])
        zipL f x@(k,_) = (\y -> (x,k,y)) <$> f x

        -- Find all holes that this hole is dependent on.
        findDependencies :: HashSet Var -> (Var, HoleInfo SpecType) -> Maybe [Var]
        findDependencies seen (v, _) | v `Set.member` seen = 
            if v `M.member` holeMap then 
                -- If we've seen this hole before, there's a cycle.
                Nothing
            else
                -- Otherwise, we're done.
                Just [] -- JP: Should we return Nothing here too?
                
        findDependencies seen' (v, hi) =
            -- Add v to seen.
            let seen = Set.insert v seen' in

            -- Lookup refinement type of v in environment.
            let reft = lookupAREnv v $ henv hi in

            -- Get set of variables in reft of v.
            -- Remove v from set of variables.
            -- Recursively find dependencies of set of variables.
            -- Check if there are any cycles in dependencies.
            -- Union all dependencies.
            -- Return all dependencies that are holes.
            
            error "TODO"

        -- JP: Does a function like this already exist?
        -- What's the right way to convert Var to Symbol?
        lookupAREnv :: Var -> AREnv t -> Maybe t
        lookupAREnv v REnv{..} = 
            let s = F.symbol v in

            -- Lookup local first.
            case M.lookup s reLocal of
                Just r -> 
                    Just r
                Nothing -> 
                    -- Lookup global next.
                    M.lookup s reGlobal
                        
