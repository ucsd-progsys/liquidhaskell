{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

module Language.Haskell.Liquid.GHC.Plugin.Types
    ( SpecComment(..)
    -- * Dealing with accumulated specs
    , LiquidLib
    , mkLiquidLib
    , libTarget
    , libDeps
    , allDeps
    , addLibDependency
    , addLibDependencies
    , SpecEnv(..)
    , CachedSpec
    , toCached
    , cachedSpecStableModuleId
    , cachedSpecModule
    , fromCached
    , insertExternalSpec
    , lookupExternalSpec

    -- * Merging specs together, the hacky, prototype-y way.
    , mergeSpecs
    , HackyEQ(..)

    -- * Acquiring and manipulating data from the typechecking phase
    , TcData
    , tcAllImports
    , tcQualifiedImports
    , tcResolvedNames
    , mkTcData

    -- * Wrapper type to talk about unoptimised things
    , Unoptimised(fromUnoptimised)
    , toUnoptimised

    , debugShowModule
    , debugShowSpecEnv
    , debugShowLiquidLib
    ) where

import           Data.Binary                             as B
import           Data.Data                                ( Data )
import           Data.Foldable
import           Text.Parsec                              ( SourcePos )
import           Text.Pretty.Simple                       ( pShowNoColor )
import           Outputable                        hiding ( (<>) )
import           GHC.Generics                      hiding ( moduleName )
import qualified Language.Haskell.Liquid.GHC.GhcMonadLike as GhcMonadLike
import           GHC                                      ( LImportDecl
                                                          , GhcRn
                                                          , Name
                                                          , TyThing
                                                          )
import           HscTypes                                 ( ModGuts )
import           TcRnTypes                                ( TcGblEnv(tcg_rn_imports) )
import           UniqFM
import           Module                                   ( ModuleName
                                                          , UnitId
                                                          , Module(..)
                                                          , moduleName
                                                          , moduleUnitId
                                                          , unitIdString
                                                          , moduleNameString
                                                          , mkModuleName
                                                          , stringToUnitId
                                                          , moduleStableString
                                                          , stableModuleCmp
                                                          )

import           Data.Map                                 ( Map )
import qualified Data.Map.Strict                         as M
import qualified Data.HashSet        as HS
import           Data.HashSet                             ( HashSet )
import           Data.Hashable
import qualified Data.Text.Lazy                          as TL

import           Language.Fixpoint.Types.Spans
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.Specs      ( QImports )
import           Language.Haskell.Liquid.Measure          ( BareSpec, Spec(..) )
import qualified Language.Haskell.Liquid.GHC.Interface   as LH
import           Language.Fixpoint.Types.Names            ( Symbol )


import Data.Coerce
import qualified Data.List as L


data LiquidLib = LiquidLib
  {  llTarget :: BareSpec
  -- ^ The target 'BareSpec'.
  ,  llDeps   :: HashSet CachedSpec
  -- ^ The specs which were necessary to produce the target 'BareSpec'.
  } deriving (Show, Generic)

instance B.Binary LiquidLib

debugShowLiquidLib :: LiquidLib -> String
debugShowLiquidLib = TL.unpack . pShowNoColor

-- | Creates a new 'LiquidLib' with no dependencies.
mkLiquidLib :: BareSpec -> LiquidLib
mkLiquidLib s = LiquidLib s mempty

addLibDependency :: CachedSpec -> LiquidLib -> LiquidLib
addLibDependency dep lib = lib { llDeps = HS.insert dep (llDeps lib) }

addLibDependencies :: HashSet CachedSpec -> LiquidLib -> LiquidLib
addLibDependencies deps lib = lib { llDeps = deps <> (llDeps lib) }

libTarget :: LiquidLib -> BareSpec
libTarget = llTarget

libDeps :: LiquidLib -> HashSet CachedSpec
libDeps = llDeps

-- | Extracts all the dependencies from a collection of 'LiquidLib's.
allDeps :: Foldable f => f LiquidLib -> HashSet CachedSpec
allDeps = foldl' (\acc lib -> acc <> llDeps lib) mempty

newtype SpecEnv    = SpecEnv {
    externalSpecs :: Map StableModule CachedSpec
  } deriving (Show, Eq, Semigroup, Monoid)

debugShowSpecEnv :: SpecEnv -> String
debugShowSpecEnv = TL.unpack . pShowNoColor

-- | A newtype wrapper around a 'Module' which:
-- * Allows a 'Module' to be serialised (i.e. it has a 'Binary' instance)
-- * It uses 'unitIdString' and 'moduleNameString' under the hood like 'moduleStableString'.
newtype StableModule = StableModule Module

instance Ord StableModule where
  (StableModule m1) `compare` (StableModule m2) = stableModuleCmp m1 m2

instance Eq StableModule where
  (StableModule m1) == (StableModule m2) = (m1 `stableModuleCmp` m2) == EQ

instance Show StableModule where
    show (StableModule mdl) = "Stable" ++ debugShowModule mdl

toStableModule :: Module -> StableModule
toStableModule = StableModule

instance Binary StableModule where
    put (StableModule mdl) = do
      put (unitIdString . moduleUnitId $ mdl)
      put (moduleNameString . moduleName $ mdl)

    get = do
      uidStr <- get
      mnStr  <- get
      pure $ StableModule (Module (stringToUnitId uidStr) (mkModuleName mnStr))


-- A cached spec which can be inserted into the 'SpecEnv'.
-- /INVARIANT/: A 'CachedSpec' has temination-checking disabled (i.e. 'noTerm' is called on the inner 'BareSpec').
data CachedSpec = CachedSpec StableModule BareSpec deriving (Show, Generic)

instance Binary CachedSpec

instance Eq CachedSpec where
    (CachedSpec id1 _) == (CachedSpec id2 _) = id1 == id2

instance Hashable CachedSpec where
    hashWithSalt s (CachedSpec (StableModule mdl) _) = 
      hashWithSalt s (moduleStableString mdl)

-- Convert the input 'BareSpec' into a 'CachedSpec', inforcing the invariant that termination checking
-- needs to be disabled as this is now considered safe to use for \"clients\".
toCached :: Module -> BareSpec -> CachedSpec
toCached mdl bareSpec = CachedSpec (toStableModule mdl) (LH.noTerm bareSpec)

cachedSpecStableModuleId :: CachedSpec -> String
cachedSpecStableModuleId (CachedSpec (StableModule m) _) = moduleStableString m

cachedSpecModule :: CachedSpec -> Module
cachedSpecModule (CachedSpec (StableModule m) _) = m

fromCached :: CachedSpec -> (ModName, BareSpec)
fromCached (CachedSpec (StableModule mdl) s) = (ModName SrcImport (moduleName mdl), s)

insertExternalSpec :: Module -> CachedSpec -> SpecEnv -> SpecEnv
insertExternalSpec mdl spec env = 
  env { externalSpecs = M.insert (toStableModule mdl) spec (externalSpecs env) }

lookupExternalSpec :: Module -> SpecEnv -> Maybe CachedSpec
lookupExternalSpec mdl env = M.lookup (toStableModule mdl) (externalSpecs env)

--
-- Merging specs together, the hacky way
--

newtype HackyEQ  a = HackyEQ  { unHackyEQ :: a }
newtype Distinct a = Distinct { unDistinct :: HS.HashSet a } deriving Semigroup

instance Binary a => Eq (HackyEQ a) where
  (HackyEQ a) == (HackyEQ b) = B.encode a == B.encode b

instance Binary a => Hashable (HackyEQ a) where
  hashWithSalt s (HackyEQ a) = hashWithSalt s (B.encode a)

fromDistinct :: Distinct (HackyEQ a) -> [a]
fromDistinct = coerce . HS.toList . unDistinct

toDistinct :: Binary a => [a] -> Distinct (HackyEQ a)
toDistinct = Distinct . HS.fromList . map HackyEQ

distinct :: Binary a => [a] -> [a]
distinct = fromDistinct . toDistinct

sameDeclaration :: (Loc a, Eq a) => a -> a -> Bool
sameDeclaration x1 x2 = x1 == x2 && (srcSpan x1 == srcSpan x2)

mergeSpecs :: BareSpec -> BareSpec -> BareSpec
mergeSpecs s1 s2 = LH.noTerm $
  (s1 <> s2) { 
      sigs      = L.nubBy (\a b -> fst a == fst b) (sigs s1 <> sigs s2)
    , dataDecls = L.nubBy sameDeclaration (dataDecls s1 <> dataDecls s2)
    --   sigs       = L.nubBy (\a b -> fst a == fst b) (sigs s1 <> sigs s2)
    -- , asmSigs    = L.nubBy (\a b -> fst a == fst b) (asmSigs s1 <> asmSigs s2)
    -- , localSigs  = L.nubBy (\a b -> fst a == fst b) (localSigs s1 <> localSigs s2)
    -- , reflSigs   = L.nubBy (\a b -> fst a == fst b) (reflSigs s1 <> reflSigs s2)
    -- , aliases    = distinct (aliases s1 <> aliases s2)
    -- , ealiases   = distinct (ealiases s1 <> ealiases s2)
    -- , qualifiers = distinct (qualifiers s1 <> qualifiers s2)
    -- , dataDecls  = distinct (dataDecls s1 <> dataDecls s2)
    -- , measures   = distinct (measures s1 <> measures s2)
    -- , imeasures  = distinct (imeasures s1 <> imeasures s2)
    -- , cmeasures  = distinct (cmeasures s1 <> cmeasures s2)

    -- , impSigs    = distinct (impSigs s1 <> impSigs s2)
    -- , expSigs    = distinct (expSigs s1 <> expSigs s2)
    -- , invariants = distinct (invariants s1 <> invariants s2)
    -- , ialiases   = distinct (ialiases s1 <> ialiases s2)
    -- , imports    = distinct (imports s1 <> imports s2)
    -- , newtyDecls = distinct (newtyDecls s1 <> newtyDecls s2)
    -- , includes   = distinct (includes s1 <> includes s2)
    -- , decr       = distinct (decr s1 <> decr s2)
    -- , pragmas    = distinct (pragmas s1 <> pragmas s2)
    -- , classes    = distinct (classes s1 <> classes s2)
    -- , claws      = distinct (claws s1 <> claws s2)
    -- , termexprs  = distinct (termexprs s1 <> termexprs s2)
    -- , rinstance  = distinct (rinstance s1 <> rinstance s2)
    -- , ilaws      = distinct (ilaws s1 <> ilaws s2)
    -- , dvariance  = distinct (dvariance s1 <> dvariance s2)
    }

-- | Just a small wrapper around the 'SourcePos' and the text fragment of a LH spec comment.
newtype SpecComment =
    SpecComment (SourcePos, String)
    deriving Data

newtype Unoptimised a = Unoptimised { fromUnoptimised :: a }

toUnoptimised :: a -> Unoptimised a
toUnoptimised = Unoptimised

-- | Data which can be \"safely\" passed to the \"Core\" stage of the pipeline.
-- The notion of \"safely\" here is a bit vague: things like imports are somewhat
-- guaranteed not to change, but things like identifiers might, so they shouldn't
-- land here.
data TcData = TcData {
    tcAllImports       :: HS.HashSet Symbol
  , tcQualifiedImports :: QImports
  , tcResolvedNames    :: [(Name, Maybe TyThing)]
  }

instance Outputable TcData where
    ppr (TcData{..}) = 
          text "TcData { imports  = " <+> text (show $ HS.toList tcAllImports)
      <+> text "       , qImports = " <+> text (show tcQualifiedImports)
      <+> text "       , names    = " <+> ppr tcResolvedNames
      <+> text " }"

-- | Constructs a 'TcData' out of a 'TcGblEnv'.
mkTcData :: GhcMonadLike.TypecheckedModule -> [(Name, Maybe TyThing)] -> TcData
mkTcData tcModule resolvedNames = TcData {
    tcAllImports       = LH.allImports       (GhcMonadLike.tm_renamed_source tcModule)
  , tcQualifiedImports = LH.qualifiedImports (GhcMonadLike.tm_renamed_source tcModule)
  , tcResolvedNames    = resolvedNames
  }

debugShowModule :: Module -> String
debugShowModule m = showSDocUnsafe $
                     text "Module { unitId = " <+> ppr (moduleUnitId m)
                 <+> text ", name = " <+> ppr (moduleName m) 
                 <+> text " }"
