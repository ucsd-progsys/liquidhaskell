{- | This module exposes variations over the standard GHC's logging functions to work with the 'Doc'
     type from the \"pretty\" package. We would like LiquidHaskell to emit diagnostic messages using the very
     same GHC machinery, so that IDE-like programs (e.g. \"ghcid\", \"ghcide\" etc) would be able to
     correctly show errors and warnings to the users, in ther editors.

     Unfortunately, this is not possible to do out of the box because LiquidHaskell uses the 'Doc' type from
     the \"pretty\" package but GHC uses (for historical reasons) its own version. Due to the fact none of
     the constructors are exported, we simply cannot convert between the two types effortlessly, but we have
     to pay the price of a pretty-printing \"roundtrip\".
-}

module Liquid.GHC.Logging (
    fromPJDoc
  , putWarnMsg
  , putErrMsg
  , mkLongErrAt
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
          -> GHC.DynFlags
          -> GHC.WarnReason
          -> GHC.Severity
          -> GHC.SrcSpan
          -> Maybe GHC.PprStyle
          -> PJ.Doc
          -> IO ()
putLogMsg logger dynFlags reason sev srcSpan _mbStyle =
  GHC.putLogMsg logger dynFlags reason sev srcSpan . GHC.text . PJ.render

defaultErrStyle :: GHC.DynFlags -> GHC.PprStyle
defaultErrStyle _dynFlags = GHC.defaultErrStyle

putWarnMsg :: GHC.Logger -> GHC.DynFlags -> GHC.SrcSpan -> PJ.Doc -> IO ()
putWarnMsg logger dynFlags srcSpan doc =
  putLogMsg logger dynFlags GHC.NoReason GHC.SevWarning srcSpan (Just $ defaultErrStyle dynFlags) doc

putErrMsg :: GHC.Logger -> GHC.DynFlags -> GHC.SrcSpan -> PJ.Doc -> IO ()
putErrMsg logger dynFlags srcSpan doc =
  putLogMsg logger dynFlags GHC.NoReason GHC.SevError srcSpan Nothing doc

-- | Like GHC's 'mkLongErrAt', but it builds the final 'ErrMsg' out of two \"HughesPJ\"'s 'Doc's.
mkLongErrAt :: GHC.SrcSpan -> PJ.Doc -> PJ.Doc -> GHC.TcRn (GHC.MsgEnvelope GHC.DecoratedSDoc)
mkLongErrAt srcSpan msg extra = GHC.mkLongErrAt srcSpan (fromPJDoc msg) (fromPJDoc extra)
