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

import Text.PrettyPrint.HughesPJ hiding (first, sep)

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
import Language.Fixpoint.Visitor hiding (freeVars)
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
import Language.Haskell.Liquid.Visitors         hiding (freeVars)
import Language.Haskell.Liquid.PredType         hiding (freeTyVars)
import Language.Haskell.Liquid.GhcMisc          ( isInternal, collectArguments, tickSrcSpan
                                                , hasBaseTypeVar, showPpr, isDataConId
                                                , symbolFastString, dropModuleNames)
import Language.Haskell.Liquid.Misc             hiding (mapSndM)
import Language.Fixpoint.Misc
import Language.Haskell.Liquid.Literals
import Language.Haskell.Liquid.RefSplit
import Control.DeepSeq
import Language.Haskell.Liquid.Constraint.Constraint

import Language.Fixpoint.Smt.Interface


import Language.Haskell.Liquid.CoreToLogic

import CoreSyn 

import Language.Haskell.Liquid.Constraint.Types


data Actions = Auto 

data AEnv = AE { ae_axioms  :: [HAxiom] 
               , ae_binds   :: [CoreBind]
               , ae_lmap    :: LogicMap
               , ae_consts  :: [Var]  -- Data constructors and imported variables
               , ae_globals :: [Var]  -- Global definitions, like axioms
               , ae_vars    :: [Var]
               }


addBind b = modify $ \ae -> ae{ae_binds = b:ae_binds ae}
addVar  x | canIgnore x = return ()
          | otherwise   =  modify $ \ae -> ae{ae_vars  = x:ae_vars  ae}
addVars x = modify $ \ae -> ae{ae_vars  = x' ++ ae_vars  ae}
  where 
    x' = filter (not . canIgnore) x 


canIgnore v = isInternal v || isTyVar v 


type Pr = State AEnv


isAuto  v = isPrefixOfSym "auto"  $ dropModuleNames $ F.symbol v 
isProof v = isPrefixOfSym "Proof" $ dropModuleNames $ F.symbol v 


mapSndM act xys = mapM (\(x, y) -> (x,) <$> act y) xys

class Provable a where 

  expandProofs :: a -> CG a 
  expandProofs x = do as       <- haxioms  <$> get 
                      lmap      <- lmap     <$> get
                      (vs, tp)  <- (filter2 (not . canIgnore) . globalVars) <$> get 
                      return $ evalState (expProofs x) (AE as [] lmap (L.nub vs) (L.nub tp) []) 
    where
      filter2 p (xs, ys) = (filter p xs, filter p ys)

  expProofs :: a -> Pr a 
  expProofs = return  

instance Provable CoreBind where
  expProofs (NonRec x e) = NonRec x <$> expProofs e 
  expProofs (Rec xes)    = Rec <$> mapSndM expProofs xes 


instance Provable CoreExpr where
  expProofs ee@(App (Tick _ (Var f)) e) | isAuto f = expandAutoProof ee e
  expProofs ee@(App (Var f) e)          | isAuto f = expandAutoProof ee e

  expProofs (App e1 e2) = liftM2 App (expProofs e1) (expProofs e2)
  expProofs (Lam x e)   = addVar x >> liftM  (Lam x) (expProofs e)
  expProofs (Let b e)   = do b' <- expProofs b 
                             addBind b' 
                             liftM (Let b') (expProofs e)
  expProofs (Case e v t alts) = liftM2 (\e -> Case e v t) (expProofs e) (mapM expProofs alts)
  expProofs (Cast e c)   = liftM (`Cast` c) (expProofs e)
  expProofs (Tick t e)   = liftM (Tick t) (expProofs e)

  expProofs (Var v)      = return $ Var v
  expProofs (Lit l)      = return $ Lit l
  expProofs (Type t)     = return $ Type t
  expProofs (Coercion c) = return $ Coercion c 


instance Provable CoreAlt where 
  expProofs (c, xs, e) = addVars xs >> liftM (c,xs,) (expProofs e)

expandAutoProof :: CoreExpr -> CoreExpr -> Pr CoreExpr
expandAutoProof inite e 
  =  do ams <- ae_axioms  <$> get  
        bds <- ae_binds   <$> get
        lm  <- ae_lmap    <$> get 
        vs  <- ae_vars    <$> get 
        gs  <- ae_globals <$> get 
        cts <- ae_consts  <$> get 
        let le = case runToLogic lm (errOther . text) (coreToPred $ foldl (flip Let) e bds) of 
                  Left e  -> e
                  Right (ErrOther _ e) -> error $ show e  
        return $ traceShow ("\n\nI now have to prove this " ++ show e
                            ++ "\n\n With axioms     \n\n" ++ show ams
                            ++ "\n\n With variables  \n\n" ++ showPpr ((\v -> (v, varType v)) <$>vs)   
                            ++ "\n\n With constants  \n\n" ++ showPpr cts   
                            ++ "\n\n Knowledge Data Base \n\n" ++ show (runStep (cts ++ vs) $ initKnowledgeBase gs)   
                            ++ "\n\n In logic        \n\n" ++ show (showpp le)) $ inite



-- |  Knowledge: things in scope that return a Proof. 
-- | TODO: Be careful to only apply inductive hypothesis on less things.

-- type Knowledge = [CoreExpr]

newtype Instance = Inst (Var, [Var], [TemplateArgument])

data TemplateArgument = TA {ta_type :: Type, ta_instance :: TArg}

data TArg = TDone CoreExpr | TTmp Var [TemplateArgument] | THole

class HasHoles a where
  hasHoles :: a -> Bool 

instance HasHoles Instance where
  hasHoles (Inst (_, _, ts)) = any hasHoles ts 

instance HasHoles TemplateArgument where
  hasHoles (TA _ t) = hasHoles t 

instance HasHoles TArg where
    hasHoles (TDone _) = False
    hasHoles THole     = True 
    hasHoles (TTmp _ ts) = any hasHoles ts    


isTDone (TDone _) = True 
isTDone _         = False

instance Show TArg where
  show (TDone e) = "TDone : " ++ showPpr e 
  show THole     = "THole"
  show (TTmp v ts) = "TTmp for " ++ showPpr v ++ tab (show ts)

tab str = concat $ map ('\t':) (lines str) 


instance Show TemplateArgument where
  show (TA t tmp) = "\n \t\t\t\tType = " ++ showPpr t ++ 
                     "\n \t\t\t\t\tConstructors = " ++ show tmp


instance Show Instance where
  show (Inst (v, tvs, ls)) = "\nAxiom\t" ++ showPpr v ++ par (sep ", " (showShortTemplate <$> ls))

sep :: String -> [String] -> String
sep _ []     = []
sep _ [x]    = x
sep c (x:xs) = x ++ c ++ sep c xs

par :: String -> String 
par str = " ( " ++ str ++ " )"

showShortTArg :: TArg -> String
showShortTemplate :: TemplateArgument -> String 
showShortTemplate ta = showShortTArg $ ta_instance ta
showShortTArg (TDone e) = showPpr e 
showShortTArg THole     = "HOLE"
showShortTArg (TTmp v ls) = showPpr v ++ par (sep ", " (showShortTemplate <$> ls))

{-
instance Show Instance where
  show (Inst (v, tvs, ls)) = "\nInstance:\t" ++ "Axiom Name = " ++ showPpr v ++ 
                        "\n\t\t\tFree Ty Vars: " ++ showPpr tvs ++
                        "\n\t\t\tArguments: " ++ concatMap show ls
-}


runStep cds is = go iter [] is 
  where
    iter = 3
    go 0 acc is = acc
    go i acc is = let (h, noh) = L.partition hasHoles is in 
                  let is'      = runStepOne cds h in 
                  go (i-1) (acc ++ noh) is' 


-- Then split ready and runStep for the rest
runStepOne :: [Var] -> [Instance] -> [Instance]
runStepOne cds is =  concatMap go is
  where
    go (Inst (ax, vs, targs)) = [Inst (ax, vs, tas) | tas <- expandOneHole vs cds targs] 


expandHole :: [Var] -> [Var] -> TemplateArgument -> [TemplateArgument]
expandHole tvs cds (TA t THole)       = TA t <$> instantiateHole tvs cds t 
expandHole tvs cds (TA t (TDone e))   = [TA t $ TDone e]
expandHole tvs cds (TA t (TTmp v ts)) = (\ts' -> TA t (TTmp v ts')) <$> expandOneHole tvs cds ts 


expandOneHole :: [Var] -> [Var] -> [TemplateArgument] -> [[TemplateArgument]]
expandOneHole tvs cds ts = go [] ts 
  where
    go acc [] 
      = [reverse acc]
    go acc (TA t THole:tas)      
      = map (\ta -> (reverse acc) ++ [TA t ta] ++ tas) (instantiateHole tvs cds t)
    go acc (TA t (TDone e):tas)   
      = go (TA t (TDone e):acc) tas
    go acc (TA t (TTmp v tts):tas) 
      = map (\xs -> (reverse acc) ++ [TA t (TTmp v xs)] ++ tas) (expandOneHole (L.nub (forallTyVars (varType v) ++ tvs)) cds tts)

instantiateHole :: [Var] -> [Var] -> Type -> [TArg]
instantiateHole tvs cds t = instantiate cds <$> cvs 
   where
      cvs = filter ((isInstanceOf tvs t). resultType . varType) cds

instantiate :: [Var] -> Var -> TArg
instantiate cds v 
  | null ts
  = TDone $ Var v 
  | otherwise 
  = TTmp v (makeTemplate <$> ts)
  where
    t = varType v 
    ts = argumentTypes t


initKnowledgeBase :: [Var] -> [Instance] 
initKnowledgeBase cts = initKB <$> axioms
  where 
    axioms = filter returnsProof cts 

initKB :: Var -> Instance 
initKB v = Inst (v, tvs, makeTemplate <$> ts)
  where
    ts  = argumentTypes t 
    t   = varType v 
    tvs = forallTyVars t

makeTemplate t = TA t THole

{-
instantiateHole tvs cds (TA t Hole) = instantiate cds <$> cvs 
   where
      cvs = filter ((isInstanceOf tvs t). resultType . varType) cds
-}

returnsProof :: Var -> Bool 
returnsProof = isProof' . resultType . varType
  where
    isProof' (TyConApp tc _) = isProof tc
    isProof' _               = False 


forallTyVars (ForAllTy v t) = v : forallTyVars t 
forallTyVars  _             = []

argumentTypes = go 
  where 
    go (ForAllTy _ t) = go t 
    go (FunTy tx t)   | isClassPred tx = go t
                      | otherwise      = tx:go t
    go _              = []

resultType (ForAllTy _ t) = resultType t
resultType (FunTy _ t)    = resultType t 
resultType  t             = t 

isInstanceOf tvs t (ForAllTy v t')
  = isInstanceOf tvs t t'
isInstanceOf tvs (ForAllTy v t) t'
  = isInstanceOf (v:tvs) t t' 
isInstanceOf tvs (TyVarTy v) (TyVarTy _) -- If I replace the second type with anything, too much freedom
  | v `elem` tvs = True  
isInstanceOf tvs (FunTy t1 t2) (FunTy t1' t2')
  = isInstanceOf tvs t1 t1' && isInstanceOf tvs t2 t2'
isInstanceOf tvs (AppTy t1 t2) (AppTy t1' t2')
  = isInstanceOf tvs t1 t1' && isInstanceOf tvs t2 t2'
isInstanceOf tvs (TyConApp c ts) (TyConApp c' ts')
  = c == c' && and (zipWith (isInstanceOf tvs) ts ts') 
isInstanceOf _ (LitTy l) (LitTy l')
  = l == l'
isInstanceOf _ (TyVarTy v) (TyVarTy v')
  = v == v'
isInstanceOf _ _ _
  = False 

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

