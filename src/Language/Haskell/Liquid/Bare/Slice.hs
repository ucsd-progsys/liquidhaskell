{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE DerivingVia                #-}


-- | This module has a function that computes the "slice" i.e. subset of the `Ms.BareSpec` that 
--   we actually need to verify a given target module, so that LH doesn't choke trying to resolve 
--   names that are not actually relevant and hence, not in the GHC Environment.
--   See LH issue 1773 for more details.
-- 
--   Specifically, this module has datatypes and code for building a Specification Dependency Graph 
--   whose vertices are 'names' that need to be resolve, and edges are 'dependencies'.


module Language.Haskell.Liquid.Bare.Slice (sliceSpecs) where

-- import qualified Language.Fixpoint.Types as F
-- import qualified Data.HashMap.Strict as M
import           Language.Haskell.Liquid.Types
-- import Data.Hashable
import qualified Language.Haskell.Liquid.Measure as Ms
-- import qualified Data.HashSet as S


-------------------------------------------------------------------------------
-- | Top-level "slicing" function
-------------------------------------------------------------------------------
sliceSpecs :: GhcSrc -> Ms.BareSpec -> [(ModName, Ms.BareSpec)] -> 
        [(ModName, Ms.BareSpec)]
sliceSpecs _tgtSrc _tgtSpec specs = specs 

{- 

-------------------------------------------------------------------------------
-- | The different kinds of names we have to resolve
-------------------------------------------------------------------------------
data Label
  = Sign  -- ^ identifier signature
  | Func  -- ^ measure or reflect
  | DCon  -- ^ data constructor
  | TCon  -- ^ type constructor
  deriving (Eq, Ord, Enum, Show)

-------------------------------------------------------------------------------
-- | A dependency 'Node' is a pair of a name @LocSymbol@ and @Label@
-------------------------------------------------------------------------------
data Node = MkNode
  { nodeName  :: F.Symbol
  , nodeLabel :: Label
  }
  deriving (Eq, Ord)

instance Hashable Label where
  hashWithSalt s = hashWithSalt s . fromEnum 
instance Hashable Node where 
  hashWithSalt s MkNode {..} = hashWithSalt s (nodeName, nodeLabel) 

newtype DepGraph = MkDepGraph 
  { dGraph :: M.HashMap Node [Node] 
  }

-------------------------------------------------------------------------------
-- | A way to combine graphs of multiple modules
-------------------------------------------------------------------------------

instance Semigroup DepGraph where
  x <> y = MkDepGraph { dGraph = M.unionWith (++) (dGraph x) (dGraph y) }

instance Monoid DepGraph where
  mempty = MkDepGraph mempty

-------------------------------------------------------------------------------
-- | A function to build the dependencies for each module
-------------------------------------------------------------------------------

mkRoots :: GhcSrc -> S.HashSet Node
mkRoots = undefined

-------------------------------------------------------------------------------
-- | A function to build the dependencies for each module
-------------------------------------------------------------------------------

class Graph a where
  mkGraph :: a -> DepGraph

instance Graph [Ms.BareSpec] where
  mkGraph specs = mconcat [ mkGraph sp | sp <- specs]

instance Graph Ms.BareSpec where
  mkGraph sp = mconcat 
    [ undefined -- FIXME -- mkGraph (expSigs sp)
    ]

-------------------------------------------------------------------------------
-- | 'reachable roots g' returns the list of Node transitively reachable from roots
-------------------------------------------------------------------------------
reachable :: S.HashSet Node -> DepGraph -> S.HashSet Node
reachable roots g = undefined -- _TODO

-------------------------------------------------------------------------------
-- | Extract the dependencies 
-------------------------------------------------------------------------------

class Deps a where
  deps :: a -> [Node]

instance Deps BareType where
  deps = error "TBD:deps:bareType"

instance Deps DataDecl where
  deps = error "TBD:deps:datadecl"

instance Deps DataCtor where 
  deps = error "TBD:deps:datactor"

-}



{- 
             -- = [ (n, slice nodes sp) | (n, sp) <- specs ]
  -- where
    -- tgtGraph = mkGraph tgtSpec
    -- impGraph = mkGraph (snd <$> specs)
    -- roots    = mkRoots tgtSrc -- S.fromList . M.keys . dGraph $ tgtGraph
    -- nodes    = reachable roots (tgtGraph <> impGraph)

class Sliceable a where
  slice :: S.HashSet Node -> a -> a

instance Sliceable Ms.BareSpec where 
  slice nodes sp = sp

-}
----
{- 
These are the fields we have to worry about

unsafeFromLiftedSpec :: LiftedSpec -> Spec LocBareType F.LocSymbol
unsafeFromLiftedSpec a = Spec
  { 
  --->>> , asmSigs    = S.toList . liftedAsmSigs $ a
  --->>> , sigs       = S.toList . liftedSigs $ a
  --->>> , invariants = S.toList . liftedInvariants $ a
  --->>> , dataDecls  = S.toList . liftedDataDecls $ a
  --->>> , newtyDecls = S.toList . liftedNewtyDecls $ a
    
  , measures   = S.toList . liftedMeasures $ a
  , impSigs    = S.toList . liftedImpSigs $ a
  , expSigs    = S.toList . liftedExpSigs $ a
  , ialiases   = S.toList . liftedIaliases $ a
  , imports    = S.toList . liftedImports $ a
  , aliases    = S.toList . liftedAliases $ a
  , ealiases   = S.toList . liftedEaliases $ a
  , embeds     = liftedEmbeds a
  , qualifiers = S.toList . liftedQualifiers $ a
  , decr       = S.toList . liftedDecr $ a
  , lvars      = liftedLvars a
  , autois     = liftedAutois a
  , autosize   = liftedAutosize a
  , cmeasures  = S.toList . liftedCmeasures $ a
  , imeasures  = S.toList . liftedImeasures $ a
  , classes    = S.toList . liftedClasses $ a
  , claws      = S.toList . liftedClaws $ a
  , rinstance  = S.toList . liftedRinstance $ a
  , ilaws      = S.toList . liftedIlaws $ a
  , dvariance  = S.toList . liftedDvariance $ a
  , bounds     = liftedBounds a
  , defs       = liftedDefs a
  , axeqs      = S.toList . liftedAxeqs $ a
  }
-}


