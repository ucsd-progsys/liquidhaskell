{-# LANGUAGE OverloadedStrings #-}
module Language.Haskell.Liquid.Literals (
        literalFRefType, literalFReft, literalConst
        ) where

import TypeRep
import Literal 

import Language.Haskell.Liquid.Measure
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.RefType
import Language.Haskell.Liquid.CoreToLogic (mkLit)

import qualified Language.Fixpoint.Types as F

import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import Data.Monoid
import Control.Applicative

---------------------------------------------------------------
----------------------- Typing Literals -----------------------
---------------------------------------------------------------

makeRTypeBase (TyVarTy α)    x
  = RVar (rTyVar α) x
makeRTypeBase (TyConApp c ts) x
  = rApp c ((`makeRTypeBase` mempty) <$> ts) [] x
makeRTypeBase _              _
  = error "RefType : makeRTypeBase"

literalFRefType tce l
  = makeRTypeBase (literalType l) (addStrLen l $ literalFReft tce l)

literalFReft tce = maybe mempty F.exprReft . snd . literalConst tce

addStrLen l = F.meet r
  where
    r = case l of
          MachStr str ->
            F.reft "v" (F.PAtom F.Eq
                        (F.EApp (name strLen) [F.EVar "v"])
                        (F.ECon (F.I (fromIntegral (T.length $ T.decodeUtf8 str)))))
          _ -> mempty

-- | `literalConst` returns `Nothing` for unhandled lits because
--    otherwise string-literals show up as global int-constants
--    which blow up qualifier instantiation.

literalConst tce l         = (sort, mkLit l)
  where
    sort                   = typeSort tce $ literalType l
