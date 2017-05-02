{-# LANGUAGE CPP                       #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE ViewPatterns              #-}
{-# LANGUAGE PatternSynonyms           #-}

-- | This module contains a wrappers and utility functions for
-- accessing GHC module information. It should NEVER depend on
module Language.Haskell.Liquid.GHC.TypeRep (
  pattern FunTy, 
  module TyCoRep, 

  mkTyArg
  ) where

import TyCoRep
import Type 

-- import           Language.Haskell.Liquid.GHC.Misc (showPpr)
-- import           Language.Fixpoint.Misc (traceShow)

mkTyArg :: TyVar -> TyBinder
mkTyArg v = Named v Visible

pattern FunTy tx t = ForAllTy (Anon tx) t 

instance Eq Type where
  t1 == t2 = eqType t1 t2

instance Eq TyBinder where
  (Named v1 f1) == (Named v2 f2) = v1 == v2 && f1 == f2  
  (Anon t1)     == (Anon t2)     = t1 == t2 
  _             == _             = False 

instance Eq Coercion where
  _ == _ = True 
