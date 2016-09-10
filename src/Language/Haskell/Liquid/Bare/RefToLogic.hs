{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Language.Haskell.Liquid.Bare.RefToLogic (
    Transformable
   , txRefToLogic

  ) where

import Prelude hiding (error)

import Language.Haskell.Liquid.Types
import Language.Fixpoint.Misc (mapSnd)
import Language.Haskell.Liquid.Bare.Env

import Language.Fixpoint.Types hiding (R)


import Language.Haskell.Liquid.GHC.Misc (dropModuleUnique, dropModuleNames)



import qualified Data.HashMap.Strict as M



txRefToLogic :: (Transformable r) => LogicMap -> InlnEnv -> r -> r
txRefToLogic = tx'


class Transformable a where
  tx  :: Symbol -> Either LMap TInline -> a -> a

  tx' :: LogicMap -> InlnEnv -> a -> a
  tx' lmap imap x = M.foldrWithKey tx x limap
    where
      limap       = M.fromList ((mapSnd Left <$> (M.toList $ logic_map lmap)) ++ (mapSnd Right <$> M.toList imap))


instance (Transformable a) => (Transformable [a]) where
  tx s m xs = tx s m <$> xs

instance Transformable DataConP where
  tx s m x = x { tyConsts = tx s m (tyConsts x)
               , tyArgs   = mapSnd (tx s m) <$> tyArgs x
               , tyRes    = tx s m (tyRes x)
               }

instance Transformable TInline where
  tx s m (TI xs e) = TI xs (tx s m e)

instance (Transformable r) => Transformable (RType c v r) where
  tx s m = fmap (tx s m)

instance Transformable RReft where
  tx s m = fmap (tx s m)

instance Transformable Reft where
  tx s m (Reft (v, p)) = if v == s
                         then impossible Nothing "Transformable: v != s"
                         else Reft(v, tx s m p)

-- OLD instance Transformable Refa where
-- OLD   tx s m (RConc p)     = RConc $ tx s m p
-- OLD   tx _ _ (RKvar x sub) = RKvar x sub

instance (Transformable a, Transformable b) => Transformable (Either a b) where
  tx s m (Left  x) = Left  (tx s m x)
  tx s m (Right x) = Right (tx s m x)


txQuant :: (Functor t, Foldable t, Transformable a)
        => t (Symbol, b) -> Symbol -> Either LMap TInline -> a -> a
txQuant xss s m p
  | s `elem` (fst <$> xss) = impossible Nothing "Transformable.tx on Pred"
  | otherwise              = tx s m p

instance Transformable a => Transformable (Located a)  where
  tx s m x = x {val = tx s m (val x)} 

instance Transformable Expr where
  tx s m (EVar s')
    | cmpSymbol s s'    = mexpr s' m
    | otherwise         = EVar s'
  tx s m e@(EApp _ _)   = txEApp (s, m) e -- f (tx s m es)
  tx _ _ (ESym c)       = ESym c
  tx _ _ (ECon c)       = ECon c
  --tx _ _ (ELit l s')    = ELit l s'
  tx s m (ENeg e)       = ENeg (tx s m e)
  tx s m (EBin o e1 e2) = EBin o (tx s m e1) (tx s m e2)
  tx s m (EIte p e1 e2) = EIte (tx s m p) (tx s m e1) (tx s m e2)
  tx s m (ECst e s')    = ECst (tx s m e) s'
  tx _ _ EBot           = EBot
  tx _ _ PTrue           = PTrue
  tx _ _ PFalse          = PFalse
  tx _ _ PTop            = PTop
  tx s m (PAnd ps)       = PAnd (tx s m <$> ps)
  tx s m (POr ps)        = POr (tx s m <$> ps)
  tx s m (PNot p)        = PNot (tx s m p)
  tx s m (PImp p1 p2)    = PImp (tx s m p1) (tx s m p2)
  tx s m (PIff p1 p2)    = PIff (tx s m p1) (tx s m p2)
  tx s m (PAtom r e1 e2) = PAtom r (tx s m e1) (tx s m e2)
  tx s m (ELam (x,t) e)  = ELam (x,t) $ txQuant [(x,t)] s m e
  tx s m (PAll xss p)    = PAll xss   $ txQuant xss s m p
  tx _ _ (PExist _ _)    = panic Nothing "tx: PExist is for fixpoint internals only"
 --  tx s m (PExist xss p)  = PExist xss $ txQuant xss s m p
  tx _ _ p@(PKVar _ _)   = p
  tx _ _ p@(ETApp _ _)   = p
  tx _ _ p@(ETAbs _ _)   = p
  tx _ _ p@PGrad         = p


instance Transformable (Measure t c) where
  tx s m x = x{eqns = tx s m <$> (eqns x)}

instance Transformable (Def t c) where
        tx s m x = x{body = tx s m (body x)}

instance Transformable Body where
  tx s m (E e)   = E $ tx s m e
  tx s m (P p)   = P $ tx s m p
  tx s m (R v p) = R v $ tx s m p

mexpr :: Symbol -> Either LMap TInline -> Expr
mexpr _ (Left  (LMap _ [] e)) = e
mexpr _ (Left  (LMap s _  _)) = EVar s
mexpr _ (Right (TI _ e)) = e
-- mexpr s s' = panic Nothing ("mexpr on " ++ show s ++ "\t" ++ show s')

txEApp :: (Symbol, Either LMap TInline) -> Expr -> Expr
txEApp (s,m) e = go f
  where
    (f, es) = splitEApp e 
    go (EVar x) = txEApp' (s,m) x  (tx s m <$> es) 
    go f        = eApps (tx s m f) (tx s m <$> es)

txEApp' :: (Symbol, Either LMap TInline) -> Symbol -> [Expr] -> Expr
txEApp' (s, (Left (LMap _ xs e))) f es
  | cmpSymbol s f && length xs == length es   
  = subst (mkSubst $ zip xs es) e
  | otherwise
  = mkEApp (dummyLoc f) es

txEApp' (s, (Right (TI xs e))) f es
  | cmpSymbol s f && length xs == length es
  = subst (mkSubst $ zip xs es) e
  | otherwise
  = mkEApp (dummyLoc f) es


{-
txPApp (s, (Right (TI xs e))) f es
  | cmpSymbol s (val f)
  = subst (mkSubst $ zip xs es) e
  | otherwise
  = EApp f es

txPApp (s, m) f es = txEApp (s, m) f es
-}

cmpSymbol :: Symbol -> Symbol -> Bool
cmpSymbol s1 {- symbol in Core -} s2 {- logical Symbol-}
  =  (dropModuleUnique s1) == (dropModuleNamesAndUnique s2)
  || (dropModuleUnique s1) == (dropModuleUnique s2)


dropModuleNamesAndUnique :: Symbol -> Symbol
dropModuleNamesAndUnique = dropModuleUnique . dropModuleNames
