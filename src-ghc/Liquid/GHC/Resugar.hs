{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE UndecidableInstances      #-}

-- | This module contains functions for "resugaring" low-level GHC `CoreExpr`
--   into high-level patterns, that can receive special case handling in
--   different phases (e.g. ANF, Constraint Generation, etc.)

module Liquid.GHC.Resugar (
  -- * High-level Source Patterns
    Pattern (..)

  -- * Lift a CoreExpr into a Pattern
  , lift

  -- * Lower a pattern back into a CoreExpr
  , lower
  ) where

import qualified Data.List as L
import           Liquid.GHC.API  as Ghc hiding (PatBind)
import qualified Liquid.GHC.Misc as GM
import qualified Language.Fixpoint.Types          as F 
import qualified Text.PrettyPrint.HughesPJ        as PJ 
-- import           Debug.Trace

--------------------------------------------------------------------------------
-- | Data type for high-level patterns -----------------------------------------
--------------------------------------------------------------------------------

data Pattern
  = PatBind
      { patE1  :: !CoreExpr
      , patX   :: !Var
      , patE2  :: !CoreExpr
      , patM   :: !Type
      , patDct :: !CoreExpr
      , patTyA :: !Type
      , patTyB :: !Type
      , patFF  :: !Var
      }                      -- ^ e1 >>= \x -> e2

  | PatReturn                -- return @ m @ t @ $dT @ e
     { patE    :: !CoreExpr  -- ^ e
     , patM    :: !Type      -- ^ m
     , patDct  :: !CoreExpr  -- ^ $dT
     , patTy   :: !Type      -- ^ t
     , patRet  :: !Var       -- ^ "return"
     }

  | PatProject               -- (case xe as x of C [x1,...,xn] -> xi) : ty
    { patXE    :: !Var       -- ^ xe
    , patX     :: !Var       -- ^ x
    , patTy    :: !Type      -- ^ ty
    , patCtor  :: !DataCon   -- ^ C
    , patBinds :: ![Var]     -- ^ [x1,...,xn]
    , patIdx   :: !Int       -- ^ i :: NatLT {len patBinds}
    }

  | PatSelfBind              -- let x = e in x
    { patX     :: !Var       -- ^ x
    , patE     :: !CoreExpr  -- ^ e
    }

  | PatSelfRecBind           -- letrec x = e in x
    { patX     :: !Var       -- ^ x
    , patE     :: !CoreExpr  -- ^ e
    }

instance F.PPrint Pattern where 
  pprintTidy  = ppPat

ppPat :: F.Tidy -> Pattern -> PJ.Doc 
ppPat k (PatReturn e m d t rv) = 
  "PatReturn: " 
  PJ.$+$ 
  F.pprintKVs k
    [ ("rv" :: PJ.Doc, GM.pprDoc rv) 
    , ("e " :: PJ.Doc, GM.pprDoc e) 
    , ("m " :: PJ.Doc, GM.pprDoc m) 
    , ("$d" :: PJ.Doc, GM.pprDoc d) 
    , ("t " :: PJ.Doc, GM.pprDoc t) 
    ] 
ppPat _ _  = "TODO: PATTERN" 
    

_mbId :: CoreExpr -> Maybe Var
_mbId (Var x)    = Just x
_mbId (Tick _ e) = _mbId e
_mbId _          = Nothing

--------------------------------------------------------------------------------
-- | Lift expressions into High-level patterns ---------------------------------
--------------------------------------------------------------------------------
lift :: CoreExpr -> Maybe Pattern
--------------------------------------------------------------------------------
lift e = exprArgs e (collectArgs e)

exprArgs :: CoreExpr -> (CoreExpr, [CoreExpr]) -> Maybe Pattern
exprArgs _e (Var op, [Type m, d, Type a, Type b, e1, Lam x e2])
  | op `is` Ghc.bindMName
  = Just (PatBind e1 x e2 m d a b op)

exprArgs (Case (Var xe) x t [Alt (DataAlt c) ys (Var y)]) _
  | Just i <- y `L.elemIndex` ys
  = Just (PatProject xe x t c ys i)


{- TEMPORARILY DISABLED: TODO-REBARE; in reality it hasn't been working AT ALL 
   since at least the GHC 8.2.1 port (?) because the TICKs get in the way 
   of recognizing the pattern? Anyways, messes up 

     tests/pattern/pos/Return00.hs  

   because we treat _all_ types of the form `m a` as "invariant" in the parameter `a`.
   Looks like the above tests only pass in earlier LH versions because this pattern 
   was NOT getting tickled!

exprArgs _e (Var op, [Type m, d, Type t, e])
  | op `is` PN.returnMName
  = Just (PatReturn e m d t op)
-}

{- TEMPORARILY DISBLED

exprArgs (Let (NonRec x e) e') _
  | Just y <- _mbId e', x == y
  = Just (PatSelfBind x e)

exprArgs (Let (Rec [(x, e)]) e') _
  | Just y <- _mbId e', x == y
  = Just (PatSelfRecBind x e)

-}
exprArgs _ _
  = Nothing

is :: Var -> Name -> Bool
is v n = n == getName v

--------------------------------------------------------------------------------
-- | Lower patterns back into expressions --------------------------------------
--------------------------------------------------------------------------------
lower :: Pattern -> CoreExpr
--------------------------------------------------------------------------------
lower (PatBind e1 x e2 m d a b op)
  = Ghc.mkCoreApps (Var op) [Type m, d, Type a, Type b, e1, Lam x e2]

lower (PatReturn e m d t op)
  = Ghc.mkCoreApps (Var op) [Type m, d, Type t, e]

lower (PatProject xe x t c ys i)
  = Case (Var xe) x t [Alt (DataAlt c) ys (Var yi)] where yi = ys !! i

lower (PatSelfBind x e)
  = Let (NonRec x e) (Var x)

lower (PatSelfRecBind x e)
  = Let (Rec [(x, e)]) (Var x)
