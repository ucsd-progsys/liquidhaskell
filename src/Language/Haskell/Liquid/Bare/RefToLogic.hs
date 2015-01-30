{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Language.Haskell.Liquid.Bare.RefToLogic (
    txRefToLogic
  ) where

import Language.Haskell.Liquid.Types

import Language.Fixpoint.Types      
import Language.Fixpoint.Misc      
import Language.Fixpoint.Names      (dropModuleNames)

import qualified Data.HashMap.Strict as M

import Control.Applicative                      ((<$>))


txRefToLogic :: (Transformable r) => LogicMap -> RType c v r -> RType c v r
txRefToLogic lmap t =  tx' lmap t


class Transformable a where
	tx  :: Symbol -> LMap -> a -> a 

	tx' :: LogicMap -> a -> a
	tx' lmap x = M.foldrWithKey tx x lmap  


instance (Transformable r) => Transformable (RType c v r) where 
	tx s m = fmap (tx s m)

instance Transformable RReft where 
	tx s m = fmap (tx s m)

instance Transformable Reft where 
	tx s m (Reft(v, refas))
		= if v == s 
			then errorstar "Transformable: this should not happen"
			else Reft(v, tx s m <$> refas)

instance Transformable Refa where
	tx s m (RConc p)     = RConc $ tx s m p 
	tx _ _ (RKvar x sub) = RKvar x sub

instance Transformable Pred where
	tx _ _ PTrue           = PTrue
	tx _ _ PFalse          = PFalse
	tx _ _ PTop            = PTop
	tx s m (PAnd ps)       = PAnd (tx s m <$> ps)
	tx s m (POr ps)        = POr (tx s m <$> ps)
	tx s m (PNot p)        = PNot (tx s m p)
	tx s m (PImp p1 p2)    = PImp (tx s m p1) (tx s m p2)
	tx s m (PIff p1 p2)    = PIff (tx s m p1) (tx s m p2)
	tx s m (PBexp e)       = PBexp (tx s m e)
	tx s m (PAtom r e1 e2) = PAtom r (tx s m e1) (tx s m e2)
	tx s m (PAll xss p) 
	    = if (s `elem` (fst <$> xss)) 
	    	then errorstar "Transformable.tx on Pred: this should not happen" 
		    else PAll xss (tx s m p) 

instance Transformable Expr where
	tx s m (EVar s') 
	   | cmpSymbol s s'   = lexpr m
	   | otherwise        = EVar s'
	tx s m (EApp f es)    = txEApp (s, m) f es
	tx _ _ (ESym c)       = ESym c
	tx _ _ (ECon c)       = ECon c
	tx _ _ (ELit l s')    = ELit l s'
	tx s m (EBin o e1 e2) = EBin o (tx s m e1) (tx s m e2)
	tx s m (EIte p e1 e2) = EIte (tx s m p) (tx s m e1) (tx s m e2)
	tx s m (ECst e s')    = ECst (tx s m e) s'
	tx _ _ EBot           = EBot

txEApp (s, (LMap _ xs e)) f es 
  | cmpSymbol s (val f) 
  = subst (mkSubst $ zip xs es) e
  | otherwise  
  = EApp f es


cmpSymbol s1 {- symbol in Core -} s2 {- logical Symbol-}
  = (dropModuleNames s1) == s2  