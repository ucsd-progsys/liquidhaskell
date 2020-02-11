{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

module Language.Haskell.Liquid.GHC.Plugin.Types
    ( SpecComment(..)
    -- * Dealing with accumulated specs
    , SpecEnv(..)
    , CachedSpec(..)
    , toCached
    , fromCached
    , cachedModuleName
    , resetBaseSpecs
    , replaceBaseSpecs
    , insertExternalSpec
    -- * Acquiring and manipulating data from the typechecking phase
    , TcData
    , tcImports
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

import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Measure          ( BareSpec )

import qualified Data.Map.Strict                         as M


data SpecEnv    = SpecEnv {
    baseSpecs :: [CachedSpec]
    -- ^ The base specs shipped with LiquidHaskell.
  , externalSpecs :: Map Module CachedSpec
  } deriving Eq

data CachedSpec = CachedSpec ModName BareSpec deriving Generic

instance Eq CachedSpec where
    (CachedSpec mn1 _) == (CachedSpec mn2 _) = mn1 == mn2

toCached :: (ModName, BareSpec) -> CachedSpec
toCached = uncurry CachedSpec

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
    tcImports              :: [LImportDecl GhcRn]
  , tcResolvedNames        :: [(Name, Maybe TyThing)]
  }

instance Outputable TcData where
    ppr (TcData{tcImports}) = 
      text "TcData { imports = " <+> ppr tcImports
              <+> text "modInfo   = <someModInfo>"
              <+> text " }"

-- | Constructs a 'TcData' out of a 'TcGblEnv'.
mkTcData :: TcGblEnv -> [(Name, Maybe TyThing)] -> TcData
mkTcData tcGblEnv resolvedNames = TcData {
    tcImports              = tcg_rn_imports tcGblEnv
  , tcResolvedNames        = resolvedNames
  }

