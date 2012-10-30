{-# LANGUAGE NoMonomorphismRestriction, DeriveDataTypeable, RankNTypes, GADTs, TupleSections  #-}

module Language.Haskell.Liquid.Tidy (tidyRefType) where

-- import Data.Generics.Schemes
-- import Data.Generics.Aliases
-- import Data.Data

import Control.Monad.State
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S

import Language.Haskell.Liquid.Fixpoint
import Language.Haskell.Liquid.RefType

---------------------------------------------------------------------
---------- SYB Magic: Cleaning Reftypes Up Before Rendering ---------
---------------------------------------------------------------------

tidyRefType :: RefType -> RefType
tidyRefType = error "TODO: tidyRefType"
--tidyRefType = tidyDSymbols
--            . tidySymbols 
--            . tidyFunBinds
--            . tidyLocalRefas 
--            . tidyTyVars 

--tidyFunBinds :: RefType -> RefType
--tidyFunBinds t = everywhere (mkT $ dropBind xs) t 
--  where xs = syms t
--        dropBind :: S.HashSet Symbol -> RefType -> RefType
--        dropBind xs (RFun x t1 t2 r)
--          | x `S.member` xs = RFun x t1 t2 r
--          | otherwise       = RFun nonSymbol t1 t2 r
--        dropBind _ z        = z
--
--tidyTyVars :: RefType -> RefType
--tidyTyVars = tidy pool getS putS 
--  where getS (α :: TyVar)   = Just (symbolString $ varSymbol α)
--        putS (_ :: TyVar) x = stringTyVar x
--        pool          = [[c] | c <- ['a'..'z']] ++ [ "t" ++ show i | i <- [1..]]
--
--tidyLocalRefas :: RefType -> RefType
--tidyLocalRefas = everywhere (mkT dropLocals) 
--  where dropLocals = filter (not . Fold.any isTmp . readSymbols) . flattenRefas
--        isTmp x    = let str = symbolString x in 
--                     (anfPrefix `isPrefixOf` str) || (tempPrefix `isPrefixOf` str) 
--
--tidySymbols :: RefType -> RefType
--tidySymbols = everywhere (mkT dropSuffix) 
--  where dropSuffix = {- stringSymbol -} S . takeWhile (/= symSep) . symbolString
--        -- dropQualif = stringSymbol . dropModuleNames . symbolString 
--
--tidyDSymbols :: RefType -> RefType
--tidyDSymbols = tidy pool getS putS 
--  where getS   sy  = let str = symbolString sy in 
--                     if "ds_" `isPrefixOf` str then Just str else Nothing
--        putS _ str = stringSymbol str 
--        pool       = ["x" ++ show i | i <- [1..]]
--
readSymbols :: (Subable a) => a -> S.HashSet Symbol
readSymbols = S.fromList . syms 

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
