{-# LANGUAGE OverloadedStrings #-}
---------------------------------------------------------------------
-- | This module contains functions for cleaning up types before
--   they are rendered, e.g. in error messages or annoations.
---------------------------------------------------------------------


module Language.Haskell.Liquid.Tidy (

    -- * Tidying functions
    tidySpecType
  , tidySymbol

    -- * Tidyness tests
  , isTmpSymbol
  ) where

import Outputable   (showPpr) -- hiding (empty)
import Control.Applicative
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S
import qualified Data.List           as L
import qualified Data.Text           as T
import Data.Maybe (fromMaybe)


import Language.Fixpoint.Misc 
import Language.Fixpoint.Names              (symSepName, isPrefixOfSym, takeWhileSym)
import Language.Fixpoint.Types
import Language.Haskell.Liquid.GhcMisc      (stringTyVar) 
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.PrettyPrint
import Language.Haskell.Liquid.RefType hiding (shiftVV)

-------------------------------------------------------------------------
tidySymbol :: Symbol -> Symbol
-------------------------------------------------------------------------
tidySymbol = takeWhileSym (/= symSepName)


-------------------------------------------------------------------------
isTmpSymbol    :: Symbol -> Bool
-------------------------------------------------------------------------
isTmpSymbol x  = any (`isPrefixOfSym` x) [anfPrefix, tempPrefix, "ds_"]


-------------------------------------------------------------------------
tidySpecType :: Tidy -> SpecType -> SpecType  
-------------------------------------------------------------------------
tidySpecType k = tidyValueVars
               . tidyDSymbols
               . tidySymbols 
               . tidyLocalRefas k 
               . tidyFunBinds
               . tidyTyVars 

tidyValueVars :: SpecType -> SpecType
tidyValueVars = mapReft $ \u -> u { ur_reft = tidyVV $ ur_reft u }

tidyVV r@(Reft (va,_))
  | isJunk va = shiftVV r v'
  | otherwise = r  
  where
    v'        = if v `elem` xs then symbol ("v'" :: T.Text) else v
    v         = symbol ("v" :: T.Text)
    xs        = syms r
    isJunk    = isPrefixOfSym "x"
    
tidySymbols :: SpecType -> SpecType
tidySymbols t = substa tidySymbol $ mapBind dropBind t  
  where 
    xs         = S.fromList (syms t)
    dropBind x = if x `S.member` xs then tidySymbol x else nonSymbol  


tidyLocalRefas   :: Tidy -> SpecType -> SpecType
tidyLocalRefas k = mapReft (txStrata . txReft' k)
  where
    txReft' Full                  = id 
    txReft' Lossy                 = txReft
    txStrata (U r p l)            = U r p (txStr l) 
    txReft (U (Reft (v,ras)) p l) = U (Reft (v, dropLocals ras)) p l
    dropLocals                    = filter (not . any isTmp . syms) . flattenRefas
    isTmp x                       = any (`isPrefixOfSym` x) [anfPrefix, "ds_"]
    txStr                         = filter (not . isSVar) 



tidyDSymbols :: SpecType -> SpecType  
tidyDSymbols t = mapBind tx $ substa tx t
  where 
    tx         = bindersTx [x | x <- syms t, isTmp x]
    isTmp      = (tempPrefix `isPrefixOfSym`)

tidyFunBinds :: SpecType -> SpecType
tidyFunBinds t = mapBind tx $ substa tx t
  where
    tx         = bindersTx $ filter isTmpSymbol $ funBinds t

tidyTyVars :: SpecType -> SpecType  
tidyTyVars t = subsTyVarsAll αβs t 
  where 
    -- zz   = [(a, b) | (a, _, (RVar b _)) <- αβs]
    αβs  = zipWith (\α β -> (α, toRSort β, β)) αs βs 
    αs   = L.nub (tyVars t)
    βs   = map (rVar . stringTyVar) pool
    pool = [[c] | c <- ['a'..'z']] ++ [ "t" ++ show i | i <- [1..]]


bindersTx ds   = \y -> M.lookupDefault y y m  
  where 
    m          = M.fromList $ zip ds $ var <$> [1..]
    var        = symbol . ('x' :) . show
 

tyVars (RAllP _ t)     = tyVars t
tyVars (RAllS _ t)     = tyVars t
tyVars (RAllT α t)     = α : tyVars t
tyVars (RFun _ t t' _) = tyVars t ++ tyVars t' 
tyVars (RAppTy t t' _) = tyVars t ++ tyVars t' 
tyVars (RApp _ ts _ _) = concatMap tyVars ts
tyVars (RCls _ ts)     = concatMap tyVars ts 
tyVars (RVar α _)      = [α] 
tyVars (RAllE _ _ t)   = tyVars t
tyVars (REx _ _ t)     = tyVars t
tyVars (RExprArg _)    = []
tyVars (RRTy _ _ _ t)  = tyVars t
tyVars (ROth _)        = []

subsTyVarsAll ats = go
  where 
    abm            = M.fromList [(a, b) | (a, _, (RVar b _)) <- ats]
    go (RAllT a t) = RAllT (M.lookupDefault a a abm) (go t)
    go t           = subsTyVars_meet ats t


funBinds (RAllT _ t)      = funBinds t
funBinds (RAllP _ t)      = funBinds t
funBinds (RAllS _ t)      = funBinds t
funBinds (RFun b t1 t2 _) = b : funBinds t1 ++ funBinds t2
funBinds (RApp _ ts _ _)  = concatMap funBinds ts
funBinds (RCls _ ts)      = concatMap funBinds ts 
funBinds (RAllE b t1 t2)  = b : funBinds t1 ++ funBinds t2
funBinds (REx b t1 t2)    = b : funBinds t1 ++ funBinds t2
funBinds (RVar _ _)       = [] 
funBinds (ROth _)         = []
funBinds (RRTy _ _ _ t)   = funBinds t
funBinds (RAppTy t1 t2 r) = funBinds t1 ++ funBinds t2
funBinds (RExprArg e)     = []

