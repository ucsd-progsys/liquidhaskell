{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

module Language.Haskell.Liquid.GHC.Plugin.Types
    ( SpecComment(..)
    -- * Dealing with accumulated specs
    , SpecEnv
    , CachedSpec(..)
    , WrappedSpec(..)
    , toCached
    , fromCached
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
import           Outputable
import           GHC.Generics
import           GHC                                      ( LImportDecl
                                                          , GhcRn
                                                          , Name
                                                          , TyThing
                                                          , Module
                                                          )
import           HscTypes                                 ( ModGuts )
import           TcRnTypes                                ( TcGblEnv(tcg_rn_imports) )
import           UniqFM
import           Module                                   ( ModuleName )
import           Data.Map                                 ( Map )

import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Measure          ( BareSpec )

import qualified Data.HashSet                            as HS
import           Data.HashSet                             ( HashSet )
import           Data.Hashable

type SpecEnv    = Map Module (HashSet CachedSpec)
data CachedSpec = CachedSpec ModName WrappedSpec deriving (Generic, Eq)

toCached :: (ModName, BareSpec) -> CachedSpec
toCached s = CachedSpec (fst s) (WrappedSpec . snd $ s)

fromCached :: CachedSpec -> (ModName, BareSpec)
fromCached (CachedSpec mn (WrappedSpec s)) = (mn, s)

instance Hashable CachedSpec

-- Just a test.
newtype WrappedSpec = WrappedSpec BareSpec deriving Generic

-- Lame 'Eq' instance just for testing purposes.
instance Eq WrappedSpec where
    (==) (WrappedSpec spec1) (WrappedSpec spec2) = B.encode spec1 == B.encode spec2

instance Hashable WrappedSpec where
    hashWithSalt s (WrappedSpec spec) = hashWithSalt s (B.encode spec)

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

