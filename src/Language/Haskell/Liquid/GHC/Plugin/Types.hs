{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Language.Haskell.Liquid.GHC.Plugin.Types
    ( SpecComment(..)
    -- * Threading state from the typechecking phase
    , TcData
    , tcImports
    , tcResolvedNames
    , tcUnoptimisedCoreBinds
    , mkTcData
    ) where

import Data.Data (Data)
import Text.Parsec (SourcePos)
import Outputable
import GHC (LImportDecl, GhcRn, Name, TyThing)
import CoreSyn
import TcRnTypes (TcGblEnv(tcg_rn_imports))

-- | Just a small wrapper around the 'SourcePos' and the text fragment of a LH spec comment.
newtype SpecComment =
    SpecComment (SourcePos, String)
    deriving Data

-- | Data which can be \"safely\" passed to the \"Core\" stage of the pipeline.
-- The notion of \"safely\" here is a bit vague: things like imports are somewhat
-- guaranteed not to change, but things like identifiers might, so they shouldn't
-- land here.
data TcData = TcData {
    tcImports              :: [LImportDecl GhcRn]
  , tcResolvedNames        :: [(Name, Maybe TyThing)]
  , tcUnoptimisedCoreBinds :: [CoreBind]
  }

instance Outputable TcData where
    ppr (TcData{tcImports}) = 
      text "TcData { imports = " <+> ppr tcImports
              <+> text "modInfo   = <someModInfo>"
              <+> text "coreBinds = <someCoreBinds>"
              <+> text " }"

-- | Constructs a 'TcData' out of a 'TcGblEnv'.
mkTcData :: TcGblEnv -> [(Name, Maybe TyThing)] -> [CoreBind] -> TcData
mkTcData tcGblEnv resolvedNames coreBinds = TcData {
    tcImports              = tcg_rn_imports tcGblEnv
  , tcResolvedNames        = resolvedNames
  , tcUnoptimisedCoreBinds = coreBinds
  }

