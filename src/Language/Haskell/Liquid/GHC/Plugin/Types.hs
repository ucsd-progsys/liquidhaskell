 
{-# LANGUAGE DeriveDataTypeable #-}

module Language.Haskell.Liquid.GHC.Plugin.Types
    ( SpecComment(..)
    -- * Threading state from the typechecking phase
    , TcStableData
    , tcStableImports
    , mkTcStableData
    ) where

import Data.Data (Data)
import Text.Parsec (SourcePos)
import Outputable
import GHC (LImportDecl, GhcRn)
import TcRnTypes (TcGblEnv(tcg_rn_imports))

-- | Just a small wrapper around the 'SourcePos' and the text fragment of a LH spec comment.
newtype SpecComment =
    SpecComment (SourcePos, String)
    deriving Data

-- | Data which can be \"safely\" passed to the \"Core\" stage of the pipeline.
-- The notion of \"safely\" here is a bit vague: things like imports are somewhat
-- guaranteed not to change, but things like identifiers might, so they shouldn't
-- land here.
data TcStableData = TcStableData {
  tcStableImports :: [LImportDecl GhcRn]
  } deriving Data

instance Outputable TcStableData where
    ppr (TcStableData imports) = text "TcStableData { imports = " <+> ppr imports <+> text " }"

-- | Constructs a 'TcStableData' out of a 'TcGblEnv'.
mkTcStableData :: TcGblEnv -> TcStableData
mkTcStableData tcGblEnv = TcStableData {
  tcStableImports = tcg_rn_imports tcGblEnv
  }

