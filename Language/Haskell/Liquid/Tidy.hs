module Language.Haskell.Liquid.Tidy (tidySpecType) where

import Control.Applicative
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S
import qualified Data.List           as L

import Language.Haskell.Liquid.Misc 
import Language.Haskell.Liquid.GhcMisc   (stringTyVar) 
import Language.Haskell.Liquid.FileNames (symSepName)
import Language.Haskell.Liquid.Fixpoint
import Language.Haskell.Liquid.RefType

---------------------------------------------------------------------
---------- SYB Magic: Cleaning Reftypes Up Before Rendering ---------
---------------------------------------------------------------------

tidySpecType :: SpecType -> SpecType  
tidySpecType = tidyDSymbols
            . tidySymbols 
            . tidyFunBinds
            . tidyLocalRefas 
            . tidyTyVars 

tidyFunBinds :: SpecType -> SpecType
tidyFunBinds t = mapBind (\x -> if x `S.member` xs then x else nonSymbol) t  
  where xs     = S.fromList (syms t)

tidyLocalRefas :: SpecType -> SpecType
tidyLocalRefas = mapReft (txReft)
  where 
    txReft (U (FReft    (Reft (v,ras))) p) = U (FReft    (Reft (v, dropLocals ras))) p
    txReft (U (FSReft s (Reft (v,ras))) p) = U (FSReft s (Reft (v, dropLocals ras))) p
    dropLocals            = filter (not . any isTmp . syms) . flattenRefas
    isTmp x               = let str = symbolString x in 
                                (anfPrefix `L.isPrefixOf` str) || (tempPrefix `L.isPrefixOf` str) 

tidySymbols :: SpecType -> SpecType  
tidySymbols = substf dropSuffix
  where 
    dropSuffix = EVar . {- stringSymbol -} S . takeWhile (/= symSepName) . symbolString
    -- dropQualif = stringSymbol . dropModuleNames . symbolString 

tidyDSymbols :: SpecType -> SpecType  
tidyDSymbols t = mapBind tx $ subst su $ t
  where 
    tx y = M.lookupDefault y y (M.fromList dxs) 
    su   = mkSubst (mapSnd EVar <$> dxs)
    dxs  = zip ds (var <$> [1..])
    ds   = [ x | x <- syms t, isDs x ]
    isDs = ("ds_" `L.isPrefixOf`) . symbolString
    var  = stringSymbol . ('x' :) . show 

tidyTyVars :: SpecType -> SpecType  
tidyTyVars t = subsTyVars_meet αβs t
  where 
    αβs  = zipWith (\α β -> (α, toRSort β, β)) αs βs 
    αs   = L.nub (tyVars t)
    βs   = map (rVar . stringTyVar) pool
    pool = [[c] | c <- ['a'..'z']] ++ [ "t" ++ show i | i <- [1..]]


tyVars (RAllP _ t)     = tyVars t
tyVars (RAllT α t)     = α : tyVars t
tyVars (RFun _ t t' _) = tyVars t ++ tyVars t' 
tyVars (RApp _ ts _ _) = concatMap tyVars ts
tyVars (RCls _ ts)     = concatMap tyVars ts 
tyVars (RVar α _)      = [α] 
tyVars (REx _ _ t)     = tyVars t
tyVars (ROth _)        = []

{- 
--tidyTyVars :: RefType -> RefType
--tidyTyVars = tidy pool getS putS 
--  where getS (α :: TyVar)   = Just (symbolString $ varSymbol α)
--        putS (_ :: TyVar) x = stringTyVar x
--        pool          = [[c] | c <- ['a'..'z']] ++ [ "t" ++ show i | i <- [1..]]
--
-
-- readSymbols :: (Subable a) => a -> S.HashSet Symbol
-- readSymbols = S.fromList . syms 

---------------------------------------------------------------------------------
---------------------------------------------------------------------------------
---------------------------------------------------------------------------------

-- data TidyS = T { memo :: M.HashMap String String
--                , pool :: [String] }
-- 
-- type TidyM = State TidyS
-- 
-- sel :: String -> TidyM (Maybe String)
-- sel s 
--   = ((s `M.lookup`) . memo) `fmap` get 
-- 
-- upd ::  String -> TidyM String
-- upd s 
--   = do st <- get
--        let (s':t) = pool st
--        let m      = memo st
--        put $ st {memo = M.insert s s' m, pool = t}
--        return s'
-- 
-- rename :: String -> TidyM String
-- rename s 
--   = do so <- sel s
--        case so of 
--          Just s' -> return s'
--          Nothing -> upd s 
-- 
-- cleaner getS putS = everywhereM (mkM swiz)
--   where swiz x = case getS x of 
--                    Nothing -> return x
--                    Just s  -> liftM (putS x) (rename s)
-- 
-- tidy :: (Data b, Typeable a) => [String] -> (a -> Maybe String) -> (a -> String -> a) -> b -> b 
-- tidy pool0 getS putS z = fst $ runState act s0
--   where act      = cleaner getS putS z 
--         s0       = T { memo = M.empty, pool = pool0 }
--         
-}


