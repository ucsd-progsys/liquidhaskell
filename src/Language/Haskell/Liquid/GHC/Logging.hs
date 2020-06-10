{- | This module exposes variations over the standard GHC's logging functions to work with the 'Doc'
     type from the \"pretty\" package. We would like LiquidHaskell to emit diagnostic messages using the very
     same GHC machinery, so that IDE-like programs (e.g. \"ghcid\", \"ghcide\" etc) would be able to
     correctly show errors and warnings to the users, in ther editors.

     Unfortunately, this is not possible to do out of the box because LiquidHaskell uses the 'Doc' type from
     the \"pretty\" package but GHC uses (for historical reasons) its own version. Due to the fact none of
     the constructors are exported, we simply cannot convert between the two types effortlessly, but we have
     to pay the price of a pretty-printing \"roundtrip\".
-}

module Language.Haskell.Liquid.GHC.Logging (
    putLogMsg
  , putWarnMsg
  , putErrMsg
  , putErrMsg'
  ) where

import Data.Maybe

import qualified GHC
import qualified DynFlags as GHC
import qualified Text.PrettyPrint.HughesPJ as PJ
import qualified Outputable as O

-- | Like the original 'putLogMsg', but internally converts the input 'Doc' (from the \"pretty\" library)
-- into GHC's internal 'SDoc'.
putLogMsg :: GHC.DynFlags
          -> GHC.WarnReason
          -> GHC.Severity
          -> GHC.SrcSpan
          -> Maybe O.PprStyle
          -> PJ.Doc
          -> IO ()
putLogMsg dynFlags reason sev srcSpan mbStyle =
  GHC.putLogMsg dynFlags reason sev srcSpan style' . O.text . PJ.render
  where
    style' :: O.PprStyle
    style' = fromMaybe (O.defaultErrStyle dynFlags) mbStyle

putWarnMsg :: GHC.DynFlags -> GHC.SrcSpan -> PJ.Doc -> IO ()
putWarnMsg dynFlags srcSpan =
  putLogMsg dynFlags GHC.NoReason GHC.SevWarning srcSpan (Just $ O.defaultErrStyle dynFlags)

putErrMsg :: GHC.DynFlags -> GHC.SrcSpan -> PJ.Doc -> IO ()
putErrMsg dynFlags srcSpan =
  putLogMsg dynFlags GHC.NoReason GHC.SevError srcSpan Nothing

-- | Like 'putErrMsg', but it uses GHC's internal 'Doc'. This can be very convenient when logging things
-- which comes directly from GHC rather than LiquidHaskell.
putErrMsg' :: GHC.DynFlags -> GHC.SrcSpan -> O.SDoc -> IO ()
putErrMsg' dynFlags srcSpan =
  GHC.putLogMsg dynFlags GHC.NoReason GHC.SevError srcSpan (O.defaultErrStyle dynFlags)
