{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}  

module Language.Haskell.Liquid.Bare.Resolve (
    Resolvable(..)
  ) where

import Control.Applicative ((<$>), (<*>))
import Control.Monad.State
import Data.Char (isUpper)
import Text.Parsec.Pos

import qualified Data.List           as L
import qualified Data.Text           as T
import qualified Data.HashMap.Strict as M

import Language.Fixpoint.Names (prims)
import Language.Fixpoint.Types (Expr(..), Pred(..), Qualifier(..), Refa(..), Reft(..), Sort(..), Symbol, fTyconSymbol, symbol, symbolFTycon, symbolText)

import Language.Haskell.Liquid.Misc (secondM, third3M)
import Language.Haskell.Liquid.Types

import Language.Haskell.Liquid.Bare.Env
import Language.Haskell.Liquid.Bare.Lookup

class Resolvable a where
  resolve :: SourcePos -> a -> BareM a

instance Resolvable a => Resolvable [a] where
  resolve = mapM . resolve

instance Resolvable Qualifier where
  resolve _ (Q n ps b l) = Q n <$> mapM (secondM (resolve l)) ps <*> resolve l b <*> return l

instance Resolvable Pred where
  resolve l (PAnd ps)       = PAnd    <$> resolve l ps
  resolve l (POr  ps)       = POr     <$> resolve l ps
  resolve l (PNot p)        = PNot    <$> resolve l p
  resolve l (PImp p q)      = PImp    <$> resolve l p  <*> resolve l q
  resolve l (PIff p q)      = PIff    <$> resolve l p  <*> resolve l q
  resolve l (PBexp b)       = PBexp   <$> resolve l b
  resolve l (PAtom r e1 e2) = PAtom r <$> resolve l e1 <*> resolve l e2
  resolve l (PAll vs p)     = PAll    <$> mapM (secondM (resolve l)) vs <*> resolve l p
  resolve _ p               = return p

instance Resolvable Expr where
  resolve l (EVar s)       = EVar   <$> resolve l s
  resolve l (EApp s es)    = EApp   <$> resolve l s  <*> resolve l es
  resolve l (ENeg e)       = ENeg   <$> resolve l e
  resolve l (EBin o e1 e2) = EBin o <$> resolve l e1 <*> resolve l e2
  resolve l (EIte p e1 e2) = EIte   <$> resolve l p  <*> resolve l e1 <*> resolve l e2
  resolve l (ECst x s)     = ECst   <$> resolve l x  <*> resolve l s
  resolve _ x              = return x

instance Resolvable LocSymbol where
  resolve _ ls@(Loc l s)
    | s `elem` prims 
    = return ls
    | otherwise 
    = do env <- gets (typeAliases . rtEnv)
         case M.lookup s env of
           Nothing | isCon s -> do v <- lookupGhcVar $ Loc l s
                                   let qs = symbol v
                                   addSym (qs,v)
                                   return $ Loc l qs
           _                 -> return ls

addSym x = modify $ \be -> be { varEnv = (varEnv be) `L.union` [x] }

isCon c 
  | Just (c,_) <- T.uncons $ symbolText c = isUpper c
  | otherwise                             = False

instance Resolvable Symbol where
  resolve l x = fmap val $ resolve l $ Loc l x 

instance Resolvable Sort where
  resolve _ FInt         = return FInt
  resolve _ FReal        = return FReal
  resolve _ FNum         = return FNum
  resolve _ s@(FObj _)   = return s --FObj . S <$> lookupName env m s
  resolve _ s@(FVar _)   = return s
  resolve l (FFunc i ss) = FFunc i <$> resolve l ss
  resolve _ (FApp tc ss)
    | tcs' `elem` prims  = FApp tc <$> ss'
    | otherwise          = FApp <$> (symbolFTycon.Loc l.symbol <$> lookupGhcTyCon tcs) <*> ss'
      where
        tcs@(Loc l tcs') = fTyconSymbol tc
        ss'              = resolve l ss

instance Resolvable (UReft Reft) where
  resolve l (U r p s) = U <$> resolve l r <*> resolve l p <*> return s

instance Resolvable Reft where
  resolve l (Reft (s, ras)) = Reft . (s,) <$> mapM resolveRefa ras
    where
      resolveRefa (RConc p) = RConc <$> resolve l p
      resolveRefa kv        = return kv

instance Resolvable Predicate where
  resolve l (Pr pvs) = Pr <$> resolve l pvs

instance (Resolvable t) => Resolvable (PVar t) where
  resolve l (PV n t v as) = PV n t v <$> mapM (third3M (resolve l)) as

instance Resolvable () where
  resolve _ = return 

