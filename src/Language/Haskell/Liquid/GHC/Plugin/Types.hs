{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

module Language.Haskell.Liquid.GHC.Plugin.Types
    ( SpecComment(..)
    -- * Dealing with accumulated specs
    , SpecEnv(..)
    , CachedSpec
    , toCached
    , fromCached
    , cachedModuleName
    , resetBaseSpecs
    , replaceBaseSpecs
    , insertExternalSpec

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
    ) where

import qualified Data.Binary                             as B
import           Data.Data                                ( Data )
import           Text.Parsec                              ( SourcePos )
import           Outputable                        hiding ( (<>) )
import           GHC.Generics
import qualified Language.Haskell.Liquid.GHC.GhcMonadLike as GhcMonadLike
import           GHC                                      ( LImportDecl
                                                          , GhcRn
                                                          , Name
                                                          , TyThing
                                                          , Module
                                                          , mkModuleName
                                                          )
import           HscTypes                                 ( ModGuts )
import           TcRnTypes                                ( TcGblEnv(tcg_rn_imports) )
import           UniqFM
import           Module                                   ( ModuleName )

import           Data.Map                                 ( Map )
import qualified Data.Map.Strict                         as M
import qualified Data.HashSet        as HS

import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.Specs      ( QImports )
import           Language.Haskell.Liquid.Measure          ( BareSpec, Spec(..) )
import qualified Language.Haskell.Liquid.GHC.Interface   as LH
import           Language.Fixpoint.Types.Names            ( Symbol )


import Data.Coerce
import Data.Binary             as B
import Data.Hashable
import qualified Data.List as L


data SpecEnv    = SpecEnv {
    baseSpecs :: [CachedSpec]
    -- ^ The base specs shipped with LiquidHaskell.
  , externalSpecs :: Map Module CachedSpec
  } deriving Eq

instance Semigroup SpecEnv where
  SpecEnv b1 e1 <> SpecEnv b2 e2 = SpecEnv (b1 <> b2) (e1 <> e2)

instance Monoid SpecEnv where
  mappend = (<>)
  mempty  = SpecEnv mempty mempty

-- A cached spec which can be inserted into the 'SpecEnv'.
-- /INVARIANT/: A 'CachedSpec' has temination-checking disabled (i.e. 'noTerm' is called on the inner 'BareSpec').
data CachedSpec = CachedSpec ModName BareSpec deriving (Generic, Show)

instance Eq CachedSpec where
    (CachedSpec mn1 _) == (CachedSpec mn2 _) = mn1 == mn2

-- Convert the input 'BareSpec' into a 'CachedSpec', inforcing the invariant that termination checking
-- needs to be disabled as this is now considered safe to use for \"clients\".
toCached :: (ModName, BareSpec) -> CachedSpec
toCached (mn, bareSpec) = CachedSpec mn (LH.noTerm bareSpec)

fromCached :: CachedSpec -> (ModName, BareSpec)
fromCached (CachedSpec mn s) = (mn, s)

cachedModuleName :: CachedSpec -> ModuleName
cachedModuleName (CachedSpec mn _) = getModName mn

resetBaseSpecs :: SpecEnv -> SpecEnv
resetBaseSpecs env = env { baseSpecs = mempty }

replaceBaseSpecs :: [CachedSpec] -> SpecEnv -> SpecEnv
replaceBaseSpecs specs env = env { baseSpecs = specs }

insertExternalSpec :: Module -> CachedSpec -> SpecEnv -> SpecEnv
insertExternalSpec mdl spec env = env { externalSpecs = M.insert mdl spec (externalSpecs env) }

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

mergeSpecs :: BareSpec -> BareSpec -> BareSpec
mergeSpecs s1 s2 = LH.noTerm $
  (s1 <> s2) { 
      sigs       = distinct (sigs s1 <> sigs s2)
    , asmSigs    = distinct (asmSigs s1 <> asmSigs s2)
    , aliases    = distinct (aliases s1 <> aliases s2)
    , ealiases   = distinct (ealiases s1 <> ealiases s2)
    , qualifiers = distinct (qualifiers s1 <> qualifiers s2)
    , dataDecls  = distinct (dataDecls s1 <> dataDecls s2)
    , measures   = distinct (measures s1 <> measures s2)
    , imeasures  = distinct (imeasures s1 <> imeasures s2)
    , cmeasures  = distinct (cmeasures s1 <> cmeasures s2)

    , impSigs    = distinct (impSigs s1 <> impSigs s2)
    , expSigs    = distinct (expSigs s1 <> expSigs s2)
    , localSigs  = distinct (localSigs s1 <> localSigs s2)
    , reflSigs   = distinct (reflSigs s1 <> reflSigs s2)
    , invariants = distinct (invariants s1 <> invariants s2)
    , ialiases   = distinct (ialiases s1 <> ialiases s2)
    , imports    = distinct (imports s1 <> imports s2)
    , newtyDecls = distinct (newtyDecls s1 <> newtyDecls s2)
    , includes   = distinct (includes s1 <> includes s2)
    , decr       = distinct (decr s1 <> decr s2)
    , pragmas    = distinct (pragmas s1 <> pragmas s2)
    , classes    = distinct (classes s1 <> classes s2)
    , claws      = distinct (claws s1 <> claws s2)
    , termexprs  = distinct (termexprs s1 <> termexprs s2)
    , rinstance  = distinct (rinstance s1 <> rinstance s2)
    , ilaws      = distinct (ilaws s1 <> ilaws s2)
    , dvariance  = distinct (dvariance s1 <> dvariance s2)
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

