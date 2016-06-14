
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}

---------------------------------------------------------------------
-- | This module contains functions for cleaning up types before
--   they are rendered, e.g. in error messages or annoations,
--   and also some PPrint instances that rely upon tidying.
---------------------------------------------------------------------

module Language.Haskell.Liquid.UX.Tidy (

    -- * Tidying functions
    tidySpecType
  , tidySymbol

    -- * Tidyness tests
  , isTmpSymbol

    -- * Panic and Exit
  , panicError

    -- * Final result
  , Result (..)

    -- * Error to UserError
  , errorToUserError

    -- * MOVE TO TYPES
  , cinfoError
  ) where

import           Data.Hashable
import           Prelude                                   hiding (error)

import qualified Data.HashMap.Strict                       as M
import qualified Data.HashSet                              as S
import qualified Data.List                                 as L
import qualified Data.Text                                 as T


import qualified Control.Exception                         as Ex

import           Language.Haskell.Liquid.GHC.Misc          (showPpr, stringTyVar)

import           Language.Fixpoint.Types                   hiding (Result, SrcSpan, Error)
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Types.RefType     (rVar, subsTyVars_meet, FreeVar)
import           Language.Haskell.Liquid.Types.PrettyPrint





import           Data.Generics                             (everywhere, mkT)
import           Text.PrettyPrint.HughesPJ


------------------------------------------------------------------------
-- | Converting Results To Answers -------------------------------------
------------------------------------------------------------------------

class Result a where
  result :: a -> FixResult UserError

instance Result UserError where
  result e = Crash [e] ""

instance Result [Error] where
  result es = Crash (errorToUserError <$> es) ""

instance Result Error where
  result e  = result [e] --  Crash [pprint e] ""

instance Result (FixResult Cinfo) where
  result = fmap (errorToUserError . cinfoError)

errorToUserError :: Error -> UserError
errorToUserError = fmap ppSpecTypeErr

-- TODO: move to Types.hs
cinfoError :: Cinfo -> Error
cinfoError (Ci _ (Just e)) = e
cinfoError (Ci l _)        = ErrOther l (text $ "Cinfo:" ++ showPpr l)

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

tidyVV :: Reft -> Reft
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
    txStrata (MkUReft r p l)      = MkUReft r p (txStr l)
    txReft u                      = u { ur_reft = mapPredReft dropLocals $ ur_reft u }
    dropLocals                    = pAnd . filter (not . any isTmp . syms) . conjuncts
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
    αβs  = zipWith (\α β -> (α, toRSort β, β)) αs βs
    αs   = L.nub (tyVars t)
    βs   = map (rVar . stringTyVar) pool
    pool = [[c] | c <- ['a'..'z']] ++ [ "t" ++ show i | i <- [1..]]


bindersTx :: [Symbol] -> Symbol -> Symbol
bindersTx ds   = \y -> M.lookupDefault y y m
  where
    m          = M.fromList $ zip ds $ var <$> [1..]
    var        = symbol . ('x' :) . show


tyVars :: RType t a t1 -> [a]
tyVars (RAllP _ t)     = tyVars t
tyVars (RAllS _ t)     = tyVars t
tyVars (RAllT α t)     = α : tyVars t
tyVars (RFun _ t t' _) = tyVars t ++ tyVars t'
tyVars (RAppTy t t' _) = tyVars t ++ tyVars t'
tyVars (RApp _ ts _ _) = concatMap tyVars ts
tyVars (RVar α _)      = [α]
tyVars (RAllE _ _ t)   = tyVars t
tyVars (REx _ _ t)     = tyVars t
tyVars (RExprArg _)    = []
tyVars (RRTy _ _ _ t)  = tyVars t
tyVars (RHole _)       = []

subsTyVarsAll
  :: (Eq k, Hashable k,
      Reftable r, TyConable c, SubsTy k (RType c k ()) c,
      SubsTy k (RType c k ()) r, SubsTy k (RType c k ()) (RType c k ()),
      FreeVar c k)
   => [(k, RType c k (), RType c k r)] -> RType c k r -> RType c k r
subsTyVarsAll ats = go
  where
    abm            = M.fromList [(a, b) | (a, _, RVar b _) <- ats]
    go (RAllT a t) = RAllT (M.lookupDefault a a abm) (go t)
    go t           = subsTyVars_meet ats t


funBinds :: RType t t1 t2 -> [Symbol]
funBinds (RAllT _ t)      = funBinds t
funBinds (RAllP _ t)      = funBinds t
funBinds (RAllS _ t)      = funBinds t
funBinds (RFun b t1 t2 _) = b : funBinds t1 ++ funBinds t2
funBinds (RApp _ ts _ _)  = concatMap funBinds ts
funBinds (RAllE b t1 t2)  = b : funBinds t1 ++ funBinds t2
funBinds (REx b t1 t2)    = b : funBinds t1 ++ funBinds t2
funBinds (RVar _ _)       = []
funBinds (RRTy _ _ _ t)   = funBinds t
funBinds (RAppTy t1 t2 _) = funBinds t1 ++ funBinds t2
funBinds (RExprArg _)     = []
funBinds (RHole _)        = []


--------------------------------------------------------------------------------
-- | Show an Error, then crash
--------------------------------------------------------------------------------
panicError :: {-(?callStack :: CallStack) =>-} Error -> a
--------------------------------------------------------------------------------
panicError = Ex.throw

-- ^ This function is put in this module as
--   it depends on the Exception instance,
--   which depends on the PPrint instance,
--   which depends on tidySpecType.

--------------------------------------------------------------------------------
-- | Pretty Printing Error Messages --------------------------------------------
--------------------------------------------------------------------------------

-- | Need to put @PPrint Error@ instance here (instead of in Types),
--   as it depends on @PPrint SpecTypes@, which lives in this module.

instance PPrint (CtxError Doc) where
  pprintTidy k ce = ppError k (ctCtx ce) $ ctErr ce

instance PPrint (CtxError SpecType) where
  pprintTidy k ce = ppError k (ctCtx ce) $ ppSpecTypeErr <$> ctErr ce

instance PPrint Error where
  pprintTidy k = ppError k empty . fmap ppSpecTypeErr

ppSpecTypeErr :: SpecType -> Doc
ppSpecTypeErr = rtypeDoc     Lossy
              . tidySpecType Lossy
              . fmap (everywhere (mkT noCasts))
  where
    noCasts (ECst x _) = x
    noCasts e          = e

instance Show Error where
  show = showpp

instance Ex.Exception Error
instance Ex.Exception [Error]
