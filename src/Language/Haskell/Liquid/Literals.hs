module Language.Haskell.Liquid.Literals (
	literalFRefType, literalFReft, literalConst
	) where 

import Type
import TypeRep
import Literal

import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.RefType
import Language.Haskell.Liquid.CoreToLogic (mkLit)

import Language.Fixpoint.Types (exprReft)

import Data.Monoid
---------------------------------------------------------------
----------------------- Typing Literals -----------------------
---------------------------------------------------------------

-- makeRTypeBase :: Type -> Reft -> RefType 
makeRTypeBase (TyVarTy α)    x       
  = RVar (rTyVar α) x 
makeRTypeBase (TyConApp c _) x 
  = rApp c [] [] x
makeRTypeBase _              _
  = error "RefType : makeRTypeBase"

literalFRefType tce l 
  = makeRTypeBase (literalType l) (literalFReft tce l) 

literalFReft tce = maybe mempty exprReft . snd . literalConst tce

 -- exprReft . snd . literalConst tce 

-- | `literalConst` returns `Nothing` for unhandled lits because
--    otherwise string-literals show up as global int-constants 
--    which blow up qualifier instantiation. 

literalConst tce l         = (sort, mkLit l)
  where 
    sort                   = typeSort tce $ literalType l 

