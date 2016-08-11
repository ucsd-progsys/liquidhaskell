{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Language.Haskell.Liquid.Bare.Resolve (
    Resolvable(..)
  ) where


import           Prelude                             hiding (error)
import           Var

import           Control.Monad.State
import           Data.Char                           (isUpper)
import           Text.Parsec.Pos

import qualified Data.List                           as L

import qualified Data.HashMap.Strict                 as M

-- import           Language.Fixpoint.Misc              (traceShow)
import           Language.Fixpoint.Types.Names       (prims, unconsSym)
import Language.Fixpoint.Types (Expr(..),
                                Qualifier(..),
                                Reft(..),
                                Sort(..),
                                Symbol,
                                fTyconSymbol,
                                symbol,
                                symbolFTycon)

import           Language.Haskell.Liquid.Misc        (secondM, third3M)
import           Language.Haskell.Liquid.Types

import           Language.Haskell.Liquid.Bare.Env
import           Language.Haskell.Liquid.Bare.Lookup

import           Data.Maybe                          (fromMaybe)
        
class Resolvable a where
  resolve :: SourcePos -> a -> BareM a

instance Resolvable a => Resolvable [a] where
  resolve = mapM . resolve

instance Resolvable Qualifier where
  resolve _ (Q n ps b l) = Q n <$> mapM (secondM (resolve l)) ps <*> resolve l b <*> return l


instance Resolvable Expr where
  resolve l (EVar s)        = EVar   <$> resolve l s
  resolve l (EApp s es)     = EApp   <$> resolve l s  <*> resolve l es
  resolve l (ENeg e)        = ENeg   <$> resolve l e
  resolve l (EBin o e1 e2)  = EBin o <$> resolve l e1 <*> resolve l e2
  resolve l (EIte p e1 e2)  = EIte   <$> resolve l p  <*> resolve l e1 <*> resolve l e2
  resolve l (ECst x s)      = ECst   <$> resolve l x  <*> resolve l s
  resolve l (PAnd ps)       = PAnd    <$> resolve l ps
  resolve l (POr  ps)       = POr     <$> resolve l ps
  resolve l (PNot p)        = PNot    <$> resolve l p
  resolve l (PImp p q)      = PImp    <$> resolve l p  <*> resolve l q
  resolve l (PIff p q)      = PIff    <$> resolve l p  <*> resolve l q
  resolve l (PAtom r e1 e2) = PAtom r <$> resolve l e1 <*> resolve l e2
  resolve l (ELam (x,t) e)  = ELam    <$> ((,) <$> resolve l x <*> resolve l t) <*> resolve l e
  resolve l (PAll vs p)     = PAll    <$> mapM (secondM (resolve l)) vs <*> resolve l p
  resolve l (ETApp e s)     = ETApp   <$> resolve l e <*> resolve l s 
  resolve l (ETAbs e s)     = ETAbs   <$> resolve l e <*> resolve l s 
  resolve _ (PKVar k s)     = return $ PKVar k s 
  resolve l (PExist ss e)   = PExist ss <$> resolve l e
  resolve _ (ESym s)        = return $ ESym s 
  resolve _ (ECon c)        = return $ ECon c 
  resolve _ PGrad           = return PGrad 

instance Resolvable LocSymbol where
  resolve _ ls@(Loc l l' s)
    | s `elem` prims
    = return ls
    | otherwise
    = do env <- gets (typeAliases . rtEnv)
         case M.lookup s env of
           Nothing | isCon s -> do v <- lookupGhcVar ls
                                   let qs = symbol v
                                   addSym (qs, v)
                                   return $ Loc l l' qs
           _                 -> return ls

addSym :: MonadState BareEnv m => (Symbol, Var) -> m ()
addSym x = modify $ \be -> be { varEnv = varEnv be `L.union` [x] }

isCon :: Symbol -> Bool
isCon s
  | Just (c,_) <- unconsSym s = isUpper c
  | otherwise                 = False

instance Resolvable Symbol where
  resolve l x = fmap val $ resolve l $ Loc l l x

instance Resolvable Sort where
  resolve _ FInt          = return FInt
  resolve _ FReal         = return FReal
  resolve _ FNum          = return FNum
  resolve _ FFrac         = return FFrac
  resolve _ s@(FObj _)    = return s --FObj . S <$> lookupName env m s
  resolve _ s@(FVar _)    = return s
  resolve l (FAbs i  s)   = FAbs i <$> (resolve l s)
  resolve l (FFunc s1 s2) = FFunc <$> (resolve l s1) <*> (resolve l s2)
  resolve _ (FTC c)
    | tcs' `elem` prims   = FTC <$> return c
    | otherwise           = do ty     <- lookupGhcTyCon tcs
                               emb    <- embeds <$> get
                               let ftc = symbolFTycon $ Loc l l' $ symbol ty
                               return  $ FTC $ fromMaybe ftc (M.lookup ty emb)
    where
      tcs@(Loc l l' tcs') = fTyconSymbol c
  resolve l (FApp t1 t2) = FApp <$> resolve l t1 <*> resolve l t2

instance Resolvable (UReft Reft) where
  resolve l (MkUReft r p s) = MkUReft <$> resolve l r <*> resolve l p <*> return s

instance Resolvable Reft where
  resolve l (Reft (s, ra)) = Reft . (s,) <$> resolve l ra

instance Resolvable Predicate where
  resolve l (Pr pvs) = Pr <$> resolve l pvs

instance (Resolvable t) => Resolvable (PVar t) where
  resolve l (PV n t v as) = PV n t v <$> mapM (third3M (resolve l)) as

instance Resolvable () where
  resolve _ = return
