{-# LANGUAGE DeriveFoldable            #-}
{-# LANGUAGE DeriveTraversable         #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE PatternGuards             #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Language.Haskell.Liquid.Constraint.Axioms (expandProofs) where 


{-
import CoreUtils     (exprType)
import MkCore
import Coercion
import DataCon
import Pair
import CoreSyn
import SrcLoc
import Type
import TyCon
import PrelNames
import TypeRep
import Class            (Class, className)
import Var
import Kind
import Id
import IdInfo
import Name
import NameSet
import TypeRep
import Unique 

import Text.PrettyPrint.HughesPJ hiding (first)

import Control.Monad.State

import Control.Applicative      ((<$>), (<*>), Applicative)

import Data.Monoid              (mconcat, mempty, mappend)
import Data.Maybe               (fromMaybe, catMaybes, fromJust, isJust)
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S
import qualified Data.List           as L
import qualified Data.Text           as T
import Data.Bifunctor
import Data.List (foldl')
import qualified Data.Foldable    as F
import qualified Data.Traversable as T

import Text.Printf

import qualified Language.Haskell.Liquid.CTags      as Tg
import Language.Fixpoint.Sort (pruneUnsortedReft)
import Language.Fixpoint.Visitor
import Language.Fixpoint.Names

import Language.Haskell.Liquid.Fresh

import qualified Language.Fixpoint.Types            as F

import Language.Haskell.Liquid.Names
import Language.Haskell.Liquid.Dictionaries
import Language.Haskell.Liquid.Variance
import Language.Haskell.Liquid.Types            hiding (binds, Loc, loc, freeTyVars, Def)
import Language.Haskell.Liquid.Strata
import Language.Haskell.Liquid.Bounds
import Language.Haskell.Liquid.RefType
import Language.Haskell.Liquid.Visitors
import Language.Haskell.Liquid.PredType         hiding (freeTyVars)
import Language.Haskell.Liquid.GhcMisc          ( isInternal, collectArguments, tickSrcSpan
                                                , hasBaseTypeVar, showPpr, isDataConId
                                                , symbolFastString)
import Language.Haskell.Liquid.Misc
import Language.Fixpoint.Misc
import Language.Haskell.Liquid.Literals
import Language.Haskell.Liquid.RefSplit
import Control.DeepSeq
import Language.Haskell.Liquid.Constraint.Constraint
-}

import CoreSyn 

import Language.Haskell.Liquid.Constraint.Types


class Provable a where 
	expandProofs :: a -> CG a 
	expandProofs = return 

instance Provable CoreBind where


{-
class Provable a where
  expandProofs :: a -> CG a
  isProof      :: a -> Bool  
  simplify     :: a -> a 
  simplifyP    :: Int -> a -> a 

  simplify = simplifyP 2 


instance Provable CoreBind where
  expandProofs (NonRec x e) = NonRec x <$> expandProofs e 
  expandProofs (Rec xes)    = return $ Rec xes

  simplifyP i (NonRec x e) = NonRec x $ simplifyP i e 
  simplifyP i (Rec xes )   = Rec (second (simplifyP i) <$> xes)


instance Provable CoreExpr where
  expandProofs ee@(Let (NonRec x ex) e') = if isProof e then go [(x, ex)] e else return ee
    where
      go :: [(Var, CoreExpr)] -> CoreExpr -> CG CoreExpr
      go bs e = do let ee = substeMany (second simplify <$> bs) e 
                   ams <- haxioms <$> get  
                   return $ proveTheorem ams $ makeTheorem ee
      e = simplify e' 
  expandProofs e = return e  

  isProof e@(App (App (Var x) (Type _)) _) = traceShow ("isProof1 " ++ show (dropModuleNames $ F.symbol x) ++ "\t\t" ++ show e ) (isPrefixOfSym "prove" (dropModuleNames $ F.symbol x))
  isProof e@(App (Var x) _) = traceShow ("isProof1 " ++ show (dropModuleNames $ F.symbol x) ++ "\t\t" ++ show e ) (isPrefixOfSym "prove" (dropModuleNames $ F.symbol x))
  isProof e = traceShow ("isProof2 " ++ show e) False 


  simplifyP i (Tick _ e) = simplifyP i e 
  simplifyP i (App e (Type _)) | i >= 2 = simplifyP i e 
  simplifyP i (App e (Var x))  | i >= 2 &&  isClassPred (varType x) = simplifyP i e 
  simplifyP i (App f e) = App (simplifyP i f) (simplifyP i e)
  simplifyP i (Lam x e) | i >= 2 && isClassPred (varType x) = simplifyP i e 
  simplifyP i (Lam x e) = Lam x $ simplifyP i e 
  simplifyP i (Let bs e) = unANF (simplifyP i bs) (simplifyP i e)
  simplifyP _ e = e 


unANF (NonRec x ex) e | L.isPrefixOf "lq_anf" (show x)
  = subst (x, ex) e 
unANF b e = Let b e

data Theorem = Thm {thm_args :: [Var], thm_lhs :: CoreExpr, thm_rhs :: CoreExpr}
  deriving (Show )

makeTheorem (App _ e) = Thm bs lhs rhs 
  where 
    (bs, lhs, rhs) = grapBs [] e 
    grapBs acc (Lam x e) = grapBs (x:acc) e
    grapBs acc (App (App v lhs) rhs) | isEquality v = (acc, lhs, rhs)

isEquality _ = True 

data PStep = PSInit | PSCase PNId Var CoreExpr | PSAxiom PNId 
  deriving (Show)

data Proof = Proof { pthm :: Theorem
                   , ptr  :: PFTree 
                   }
type PNId = Int 

type PFTree = [PNode]
data PNode = PNode { pn_id   :: PNId
                   , pn_vars :: [Var]
                   , pn_expr :: CoreExpr
                   , pn_step :: PStep
                   , pn_goal :: CoreExpr
                   } 
            | PMany [PNode]


instance Show PNode where
  show pn@(PNode _ _ _ _ _) = "\n(" ++ show (pn_id pn) ++  ") Vars = " ++ show (pn_vars pn) ++  
                             "\n\t" ++ show (pn_expr pn) ++ "=?=" ++ show (pn_goal pn)  
  show (PMany ns)           = "\n\nSTART\n" ++ show ns ++ "\nEND\n\n" 

proveTheorem :: [HAxiom] -> Theorem -> CoreExpr
proveTheorem axs thm@(Thm c lhs rhs) 
  = let pf = evalState (makeProofTree axs thm) (PST 0) in 
    traceShow ("\n\nProve \n" ++ show thm ++ "\nGIVEN\n" ++ show axs ++ 
               "\n\nProof Tree \n" ++ show pf 
              ) rhs

makeProofTree :: [HAxiom] -> Theorem ->  PM ([PNode], [PNode])
makeProofTree axs thm 
  = do (i1, i2) <- freshPM
       t1 <- go [PNode i1 (thm_args thm) (thm_lhs thm) PSInit (thm_rhs thm)]
       t2 <- go [PNode i2 (thm_args thm) (thm_rhs thm) PSInit (thm_lhs thm)]
       return (t1, t2)
  where
    go (x:xs) = do cs   <- caseSplit x 
                   axms <- mapM (applyAxiom x) (axs ++ (flipSides <$> axs)) 
                   ys   <- go xs 
                   return $ cs ++ axms ++ ys
    go [] = return []  

flipSides ax = ax {alhs = arhs ax, arhs = alhs ax}

-- NV TODO: do it for the rest of the variables 
caseSplit :: PNode -> PM [PNode]
caseSplit (PNode j (x:xs) lhs _ rhs) | (TyConApp ty ts) <- varType x 
  = do is <- refreshPM ((const 0) <$> ds)
       vs <- mapM (dArgs ts) ds 
       return $ [PMany (L.zipWith3 mkNode ds vs is)]
  where 
    TyConApp ty ts = varType x 
    ds = TyCon.tyConDataCons ty 

    mkNode d vs i = 
        let e = mkConApp d (Var <$> vs) in
        PNode i (vs++xs) (subst (x, e) lhs) (PSCase j x e) (subst (x,e) rhs)

caseSplit pn@(PNode _ _ _ _ _) = return [pn]
caseSplit (PMany nds) = ((:[]) . PMany . concat) <$> mapM caseSplit nds


applyAxiom pn@(PNode j xs lhs st rhs) ax@(Axiom aid vs ts alhs lrhs) 
  = 

    return $ traceShow ("\nApply ax: " ++ show ax ++ "\n\n In \t" ++ show pn ) $ pn
  where
    θ = unifier xs vs lhs alhs 


unifier = go []
  where
    go xs vs su (Var x) (Var v) | x == v || (x, v) `elem` su = su
                                | x `elem` xs && v `elem` vs = (x,v):su
    go xs vs su (App f1 e1) (App f2 e2) = let su1 = go xs vs su f1 e1 
                                              su2 = go xs vs su f2 e2 
                                          in  L.nub (su1 ++ su2)

{-
data Axiom b s e = Axiom { aname  :: (Var, Maybe DataCon) 
                         , abinds :: [b] 
                         , atypes :: [s]
                         , alhs   :: e 
                         , arhs   :: e  
                         }
-}

dArgs ts d = go ts t  
  where
    t = dataConUserType d 
    go (ta:tas) (ForAllTy _ t) = {- (Type ta :) <$> -} go tas t
    go tas      (FunTy tx t)   = liftM2 (:) (freshVar tx) (go tas t)
    go _        t              = return []

data PST = PST {st_index :: Int}

type PM = State PST 

class Fresh a where
  freshPM :: PM a 
  refreshPM :: a -> PM a 

  refreshPM _ = freshPM

instance Fresh a => Fresh [a] where
  refreshPM [] = return [] 
  refreshPM (x:xs) = do y  <- refreshPM x
                        ys <- refreshPM xs
                        return (y:ys)

instance Fresh Int where
  freshPM = do (PST i) <- get
               put (PST (i+1))
               return i 
instance (Fresh a, Fresh b) => Fresh (a, b) where
  freshPM = do x <- freshPM
               y <- freshPM
               return (x, y)

instance Fresh Unique where
  freshPM = mkUniqueGrimily <$> freshPM 

freshVar :: Type -> PM Var 
freshVar t = do uniq <- freshPM 
                return $ mkSysLocal (symbolFastString $ "pv") uniq t 

class SubableE a where
  subst :: (Var, CoreExpr) -> a -> a 
  substeMany :: [(Var, CoreExpr)] -> a -> a 
  substeMany xs e = foldr subst e xs 

instance SubableE CoreExpr where
  subst (x, ex) (Var y) | x == y    = ex 
                        | otherwise = Var y
  subst su (App f e) = App (subst su f) (subst su e)  
  subst su (Lam x e) = Lam x (subst su e)
  subst _ _          = error "TODO Subable"


-}

