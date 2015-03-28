{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Language.Haskell.Liquid.Bare.RefToLogic (
    txRefToLogic, Transformable
  ) where

import Language.Haskell.Liquid.Types


import Language.Haskell.Liquid.Bare.Env

import Language.Fixpoint.Types hiding (Def, R)
import Language.Fixpoint.Misc
import Language.Fixpoint.Names

import qualified Data.HashMap.Strict as M

import Control.Applicative                      ((<$>))

txRefToLogic :: (Transformable r) => LogicMap -> InlnEnv -> r -> r
txRefToLogic lmap imap t =  tx' lmap imap t


class Transformable a where
        tx  :: Symbol -> (Either LMap TInline) -> a -> a

        tx' :: LogicMap -> InlnEnv -> a -> a
        tx' lmap imap x = M.foldrWithKey tx x limap
          where limap = M.fromList ((mapSnd Left <$> M.toList lmap) ++ (mapSnd Right <$> M.toList imap))


instance (Transformable a) => (Transformable [a]) where
        tx s m xs = tx s m <$> xs

instance Transformable DataConP where
        tx s m x = x{ tyConsts = tx s m (tyConsts x)
                , tyArgs   = mapSnd (tx s m) <$> (tyArgs x)
                , tyRes    = tx s m (tyRes x)
                }

instance Transformable TInline where
  tx s m (TI xs e) = TI xs (tx s m e)

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

instance (Transformable a, Transformable b) => Transformable (Either a b) where
        tx s m (Left  x) = Left  (tx s m x)
        tx s m (Right x) = Right (tx s m x)

instance Transformable Pred where
        tx _ _ PTrue           = PTrue
        tx _ _ PFalse          = PFalse
        tx _ _ PTop            = PTop
        tx s m (PAnd ps)       = PAnd (tx s m <$> ps)
        tx s m (POr ps)        = POr (tx s m <$> ps)
        tx s m (PNot p)        = PNot (tx s m p)
        tx s m (PImp p1 p2)    = PImp (tx s m p1) (tx s m p2)
        tx s m (PIff p1 p2)    = PIff (tx s m p1) (tx s m p2)
        tx s m (PBexp (EApp f es)) = txPApp (s, m) f (tx s m <$> es)
        tx s m (PBexp e)       = PBexp (tx s m e)
        tx s m (PAtom r e1 e2) = PAtom r (tx s m e1) (tx s m e2)
        tx s m (PAll xss p)
            = if (s `elem` (fst <$> xss))
                then errorstar "Transformable.tx on Pred: this should not happen"
                    else PAll xss (tx s m p)

instance Transformable Expr where
        tx s m (EVar s')
           | cmpSymbol s s'   = mexpr m
           | otherwise        = EVar s'
        tx s m (EApp f es)    = txEApp (s, m) f (tx s m <$> es)
        tx _ _ (ESym c)       = ESym c
        tx _ _ (ECon c)       = ECon c
        tx _ _ (ELit l s')    = ELit l s'
        tx s m (ENeg e)       = ENeg (tx s m e)
        tx s m (EBin o e1 e2) = EBin o (tx s m e1) (tx s m e2)
        tx s m (EIte p e1 e2) = EIte (tx s m p) (tx s m e1) (tx s m e2)
        tx s m (ECst e s')    = ECst (tx s m e) s'
        tx _ _ EBot           = EBot

instance Transformable (Measure t c) where
        tx s m x = x{eqns = tx s m <$> (eqns x)}

instance Transformable (Def c) where
        tx s m x = x{body = tx s m (body x)}

instance Transformable Body where
   tx s m (E e)   = E $ tx s m e
   tx s m (P p)   = P $ tx s m p
   tx s m (R v p) = R v $ tx s m p

mexpr (Left  (LMap _ _ e)) = e
mexpr (Right (TI _ (Right e))) = e
mexpr _ = errorstar "mexpr"

txEApp (s, (Left (LMap _ xs e))) f es
  | cmpSymbol s (val f)
  = subst (mkSubst $ zip xs es) e
  | otherwise
  = EApp f es

txEApp (s, (Right (TI xs (Right e)))) f es
  | cmpSymbol s (val f)
  = subst (mkSubst $ zip xs es) e
  | otherwise
  = EApp f es


txEApp (s, (Right (TI _ (Left _)))) f es
  | cmpSymbol s (val f)
  = errorstar "txEApp: deep internal error"
  | otherwise
  = EApp f es


txPApp (s, (Right (TI xs (Left e)))) f es
  | cmpSymbol s (val f)
  = subst (mkSubst $ zip xs es) e
  | otherwise
  = PBexp $ EApp f es

txPApp (s, m) f es = PBexp $ txEApp (s, m) f es

cmpSymbol s1 {- symbol in Core -} s2 {- logical Symbol-}
  = (dropModuleNamesAndUnique s1) == (dropModuleNamesAndUnique s2)


dropModuleNamesAndUnique = dropModuleUnique {- . dropModuleNames -}
