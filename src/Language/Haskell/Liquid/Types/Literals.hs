{-# LANGUAGE OverloadedStrings #-}

module Language.Haskell.Liquid.Types.Literals (
         literalFRefType
       , literalFReft
       , literalConst

       , mkI, mkS 
       ) where

import Prelude hiding (error)
import TypeRep
import Literal
import qualified TyCon  as TC
-- import Language.Haskell.Liquid.Measure
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.Types.RefType
import Language.Haskell.Liquid.Transforms.CoreToLogic (mkLit, mkI, mkS)


import qualified Language.Fixpoint.Types as F

-- import qualified Data.Text as T




---------------------------------------------------------------
----------------------- Typing Literals -----------------------
---------------------------------------------------------------

makeRTypeBase :: Monoid r => Type -> r -> RType RTyCon RTyVar r
makeRTypeBase (TyVarTy α)    x
  = RVar (rTyVar α) x
makeRTypeBase (TyConApp c ts) x
  = rApp c ((`makeRTypeBase` mempty) <$> ts) [] x
makeRTypeBase _              _
  = panic Nothing "RefType : makeRTypeBase"

literalFRefType :: Literal -> RType RTyCon RTyVar F.Reft
literalFRefType l
  = makeRTypeBase (literalType l) (literalFReft l)


literalFReft :: Literal -> F.Reft
literalFReft l = maybe mempty mkReft $ mkLit l

mkReft :: F.Expr -> F.Reft
mkReft = F.exprReft 
{-
mkReft e = case e of

            F.ESym (F.SL str) ->
              -- FIXME: unsorted equality is shady, better to not embed Add# as int..
              F.meet (F.uexprReft e)
                     (F.reft "v" (F.PAtom F.Eq
                                  (F.mkEApp (name strLen) [F.EVar "v"])
                                  (F.ECon (F.I (fromIntegral (T.length str))))))
            _ -> F.exprReft e
-}
-- | `literalConst` returns `Nothing` for unhandled lits because
--    otherwise string-literals show up as global int-constants
--    which blow up qualifier instantiation.

literalConst :: F.TCEmb TC.TyCon -> Literal -> (F.Sort, Maybe F.Expr)
literalConst tce l = (t, mkLit l)
  where
    t              = typeSort tce $ literalType l
