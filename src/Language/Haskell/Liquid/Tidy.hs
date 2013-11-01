module Language.Haskell.Liquid.Tidy (tidySpecType) where

import Outputable   (showPpr) -- hiding (empty)
import Control.Applicative
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S
import qualified Data.List           as L

import Language.Fixpoint.Misc 
import Language.Fixpoint.Names              (symSepName)
import Language.Fixpoint.Types
import Language.Haskell.Liquid.GhcMisc      (stringTyVar) 
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.RefType
---------------------------------------------------------------------
---------- SYB Magic: Cleaning Reftypes Up Before Rendering ---------
---------------------------------------------------------------------

tidySpecType :: SpecType -> SpecType  
tidySpecType = tidyDSymbols
             . tidySymbols 
             . tidyLocalRefas 
             . tidyFunBinds
             . tidyTyVars 

tidySymbols :: SpecType -> SpecType
tidySymbols t = substa dropSuffix $ mapBind dropBind t  
  where 
    xs         = S.fromList (syms t)
    dropBind x = if x `S.member` xs then dropSuffix x else nonSymbol  
    dropSuffix = S . takeWhile (/= symSepName) . symbolString

tidyLocalRefas :: SpecType -> SpecType
tidyLocalRefas = mapReft (txReft)
  where 
    txReft (U (Reft (v,ras)) p) = U (Reft (v, dropLocals ras)) p
    dropLocals = filter (not . any isTmp . syms) . flattenRefas
    isTmp x    = any (`L.isPrefixOf` (symbolString x)) [anfPrefix, "ds_"] 

isTmpSymbol x  = any (`L.isPrefixOf` str) [anfPrefix, tempPrefix, "ds_"]
  where str    = symbolString x


tidyDSymbols :: SpecType -> SpecType  
tidyDSymbols t = mapBind tx $ substa tx t
  where 
    tx         = bindersTx [x | x <- syms t, isTmp x]
    isTmp      = (tempPrefix `L.isPrefixOf`) . symbolString

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
    var        = stringSymbol . ('x' :) . show 
 

tyVars (RAllP _ t)     = tyVars t
tyVars (RAllT α t)     = α : tyVars t
tyVars (RFun _ t t' _) = tyVars t ++ tyVars t' 
tyVars (RAppTy t t' _) = tyVars t ++ tyVars t' 
tyVars (RApp _ ts _ _) = concatMap tyVars ts
tyVars (RCls _ ts)     = concatMap tyVars ts 
tyVars (RVar α _)      = [α] 
tyVars (RAllE _ _ t)   = tyVars t
tyVars (REx _ _ t)     = tyVars t
tyVars (RExprArg _)    = []
tyVars (RRef _)        = []
tyVars (ROth _)        = []

subsTyVarsAll ats = go
  where 
    abm            = M.fromList [(a, b) | (a, _, (RVar b _)) <- ats]
    go (RAllT a t) = RAllT (M.lookupDefault a a abm) (go t)
    go t           = subsTyVars_meet ats t


funBinds (RAllT _ t)      = funBinds t
funBinds (RAllP _ t)      = funBinds t
funBinds (RFun b t1 t2 _) = b : funBinds t1 ++ funBinds t2
funBinds (RApp _ ts _ _)  = concatMap funBinds ts
funBinds (RCls _ ts)      = concatMap funBinds ts 
funBinds (RAllE b t1 t2)  = b : funBinds t1 ++ funBinds t2
funBinds (REx b t1 t2)    = b : funBinds t1 ++ funBinds t2
funBinds (RVar _ _)       = [] 
funBinds (ROth _)         = []
funBinds (RRef _)         = []
funBinds (RAppTy t1 t2 r) = funBinds t1 ++ funBinds t2
funBinds (RExprArg e)     = []

