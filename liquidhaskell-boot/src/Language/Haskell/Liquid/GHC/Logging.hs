{- | This module exposes variations over the standard GHC's logging functions to work with the 'Doc'
     type from the \"pretty\" package. We would like LiquidHaskell to emit diagnostic messages using the very
     same GHC machinery, so that IDE-like programs (e.g. \"ghcid\", \"ghcide\" etc) would be able to
     correctly show errors and warnings to the users, in ther editors.

     Unfortunately, this is not possible to do out of the box because LiquidHaskell uses the 'Doc' type from
     the \"pretty\" package but GHC uses (for historical reasons) its own version. Due to the fact none of
     the constructors are exported, we simply cannot convert between the two types effortlessly, but we have
     to pay the price of a pretty-printing \"roundtrip\".
-}

module Language.Haskell.Liquid.GHC.Logging
  ( addTcRnUnknownMessage
  , addTcRnUnknownMessages
  , fromPJDoc
  , putWarnMsg
  ) where

import qualified Liquid.GHC.API as GHC
import qualified Text.PrettyPrint.HughesPJ as PJ

-- Unfortunately we need the import below to bring in scope 'PPrint' instances.
import Language.Haskell.Liquid.Types.Errors ()

fromPJDoc :: PJ.Doc -> GHC.SDoc
fromPJDoc = GHC.text . PJ.render

-- | Like the original 'putLogMsg', but internally converts the input 'Doc' (from the \"pretty\" library)
-- into GHC's internal 'SDoc'.
putLogMsg :: GHC.Logger
          -> GHC.Severity
          -> GHC.SrcSpan
          -> Maybe GHC.PprStyle
          -> PJ.Doc
          -> IO ()
putLogMsg logger sev srcSpan _mbStyle =
  GHC.putLogMsg
    logger
    (GHC.logFlags logger)
    (GHC.MCDiagnostic sev (GHC.ResolvedDiagnosticReason GHC.WarningWithoutFlag) Nothing)
    srcSpan . GHC.text . PJ.render

putWarnMsg :: GHC.Logger -> GHC.SrcSpan -> PJ.Doc -> IO ()
putWarnMsg logger srcSpan doc =
  putLogMsg logger GHC.SevWarning srcSpan (Just GHC.defaultErrStyle) doc

addTcRnUnknownMessage :: GHC.SrcSpan -> PJ.Doc -> GHC.TcRn ()
addTcRnUnknownMessage srcSpan = GHC.addErrAt srcSpan . GHC.mkTcRnUnknownMessage . GHC.mkPlainError [] . fromPJDoc

addTcRnUnknownMessages :: [(GHC.SrcSpan, PJ.Doc)] -> GHC.TcRn ()
addTcRnUnknownMessages = GHC.addErrs . map (fmap (GHC.mkTcRnUnknownMessage . GHC.mkPlainError [] . fromPJDoc))
