{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Language.Haskell.Liquid.GHC.Plugin.Types
    ( SpecComment(..)
    -- * Threading state from the typechecking phase
    , SpecEnv
    , TcData
    , tcImports
    , tcResolvedNames
    , mkTcData

    -- * Wrapper type to talk about unoptimised things
    , Unoptimised(fromUnoptimised)
    , toUnoptimised
    ) where

import Data.Data (Data)
import Text.Parsec (SourcePos)
import Outputable
import GHC (LImportDecl, GhcRn, Name, TyThing)
import HscTypes (ModGuts)
import TcRnTypes (TcGblEnv(tcg_rn_imports))
import UniqFM
import Module (ModuleName)

import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Measure          ( BareSpec )

type SpecEnv = UniqFM (ModName, BareSpec)

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

