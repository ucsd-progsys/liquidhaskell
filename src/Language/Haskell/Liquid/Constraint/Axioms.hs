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


import Literal 

import CoreUtils     (exprType)
import MkCore
import Coercion
import DataCon
import Pair
import CoreSyn
import SrcLoc hiding (Located)
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
import Language.Fixpoint.Files 

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

import Language.Haskell.Liquid.WiredIn (wiredSortedSyms)

import Language.Fixpoint.Smt.Interface


import Language.Haskell.Liquid.CoreToLogic

import CoreSyn 

import Language.Haskell.Liquid.Constraint.Types

import System.IO.Unsafe

data AEnv = AE { ae_axioms  :: [HAxiom] 
               , ae_binds   :: [CoreBind]
               , ae_lmap    :: LogicMap
               , ae_consts  :: [Var]  -- Data constructors and imported variables
               , ae_globals :: [Var]  -- Global definitions, like axioms
               , ae_vars    :: [Var]
               , ae_emb     :: F.TCEmb TyCon  
               , ae_lits    :: [(Symbol, F.Sort)]
               , ae_index   :: Integer 
               , ae_sigs    :: [(Symbol, SpecType)]
               , ae_target  :: FilePath
               }



addBind b = modify $ \ae -> ae{ae_binds = b:ae_binds ae}
addVar  x | canIgnore x = return ()
          | otherwise   =  modify $ \ae -> ae{ae_vars  = x:ae_vars  ae}
addVars x = modify $ \ae -> ae{ae_vars  = x' ++ ae_vars  ae}
  where 
    x' = filter (not . canIgnore) x 


getUniq :: Pr Integer 
getUniq
  =  modify (\s -> s{ae_index = 1 + (ae_index s)}) >> ae_index <$> get 

canIgnore v = isInternal v || isTyVar v 


hasBaseType = isBaseTy . varType

type Pr = State AEnv


isAuto  v = isPrefixOfSym "auto"  $ dropModuleNames $ F.symbol v 
isProof v = isPrefixOfSym "Proof" $ dropModuleNames $ F.symbol v 


normalize xts = filter hasBaseSort $ L.nub xts -- only keep isBasic things
  where
    hasBaseSort (x, s) = isBaseSort s 

isBaseSort (F.FFunc _ ss) = and $ map notFFunc ss 
isBaseSort (F.FApp s1 s2) = isBaseSort s1 && isBaseSort s2 
isBaseSort  _             = True 

notFFunc (F.FFunc _ _) = False
notFFunc _ = True 


mapSndM act xys = mapM (\(x, y) -> (x,) <$> act y) xys

class Provable a where 

  expandProofs :: GhcInfo -> [(F.Symbol, SpecType)] -> a -> CG a 
  expandProofs info sigs x 
    = do tce      <- tyConEmbed <$> get 
         lts      <- lits <$> get 
         return $ evalState (expProofs x) 
                        AE { ae_axioms  = axioms spc 
                           , ae_binds   = []
                           , ae_lmap    = logicMap spc 
                           , ae_consts  = L.nub vs
                           , ae_globals = L.nub tp
                           , ae_vars    = []
                           , ae_emb     = tce 
                           , ae_lits    = wiredSortedSyms ++ lts 
                           , ae_index   = 0 
                           , ae_sigs    = sigs
                           , ae_target  = target info  
                           }
    where
      spc        = spec info
      vs         = filter validVar (snd <$> freeSyms spc)
      tp         = filter validExp (defVars info)

      isExported = flip elemNameSet (exports $ spec info) . getName
      validVar   = not . canIgnore
      validExp x = validVar x && isExported x 


  expProofs :: a -> Pr a 
  expProofs = return  

instance Provable CoreBind where
  expProofs (NonRec x e) = NonRec x <$> expProofs e 
  expProofs (Rec xes)    = Rec <$> mapSndM expProofs xes 


instance Provable CoreExpr where
  expProofs ee@(App (App (Tick _ (Var f)) i) e) | isAuto f = grapInt i >>= expandAutoProof ee e 
  expProofs ee@(App (App (Var f) i) e)          | isAuto f = grapInt i >>= expandAutoProof ee e
  expProofs ee@(App (Tick _ (App (Tick _ (Var f)) i)) e) | isAuto f = grapInt i >>= expandAutoProof ee e
  expProofs ee@(App (Tick _ (App (Var f) i)) e)          | isAuto f = grapInt i >>= expandAutoProof ee e

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



grapInt (Var v) 
  = do bs <- ae_binds <$> get 
       let (e:_) = [ex | NonRec x ex <- bs, x == v]
       return $ go e 
  where 
    go (Tick _ e) = go e
    go (App _ l)  = go l
    go (Lit l)    = litToInt l 

    litToInt (MachInt i) = i 
    litToInt (MachInt64 i) = i 
    litToInt _             = error "litToInt: non integer literal"

grapInt (Tick _ e) =  grapInt e 
grapInt i = return 2




instance Provable CoreAlt where 
  expProofs (c, xs, e) = addVars xs >> liftM (c,xs,) (expProofs e)

expandAutoProof :: CoreExpr -> CoreExpr -> Integer -> Pr CoreExpr
expandAutoProof inite e it  
  =  do ams <- ae_axioms  <$> get  
        bds <- ae_binds   <$> get
        lm  <- ae_lmap    <$> get 
        vs  <- ae_vars    <$> get 
        gs  <- ae_globals <$> get 
        cts <- ae_consts  <$> get 
        tce <- ae_emb     <$> get 
        lts <- ae_lits    <$> get 
        i   <- getUniq
        let env = normalize (lts ++ ((\v -> (F.symbol v, typeSort tce $ varType v)) <$> vs )) -- (filter hasBaseType vs))) --  ++ gs ++ cts))
        let le = case runToLogic lm (errOther . text) (coreToPred $ foldl (flip Let) e bds) of 
                  Left e  -> e
                  Right (ErrOther _ e) -> error $ show e
        knowledge <-  runStep it ( (fst . aname <$> ams) ++ 
                                 cts ++ vs) $ initKnowledgeBase gs
        ps <- mapM instanceToLogic knowledge
        axiom <- findValid env F.PTrue [] le knowledge
        return $ traceShow ("\n\nI now have to prove this " ++ show e
                            ++ "\n\n With axioms     \n\n" ++ show ams
                            ++ "\n\n Init Knowledge  \n\n" ++ show (initKnowledgeBase gs)
                            ++ "\n\n With variables  \n\n" ++ showPpr ((\v -> (v, varType v)) <$>vs)   
                            ++ "\n\n With constants  \n\n" ++ showPpr cts   
                            ++ "\n\n Valid axiom     \n\n" ++ show axiom
                            ++ "\n\n Logical Axioms axiom     \n\n" ++ concatMap showppp (zip knowledge ps)
                            ++ "\n\n Knowledge Data Base \n\n" ++ show knowledge   
                            ++ "\n\n In logic        \n\n" ++ show (showpp le) ) $ inite



showppp (a, (_, (_, p)))
  = "\nAXIOM TO LOGIC\t" ++ show a ++ "\n\t" ++ showpp p ++ "\n\n"

freshFilePath :: Pr FilePath 
freshFilePath = 
  do fn <- ae_target <$> get  
     n  <- getUniq
     return $ (extFileName (Auto $ fromInteger n) fn)

findValid :: [(Symbol, F.Sort)] -> F.Pred -> [Instance] -> F.Pred -> [Instance] -> Pr (Maybe [Instance])
findValid env p used q is
  = do fn  <- freshFilePath
       let cxt = unsafePerformIO $ makeZ3Context fn env 
       findValid' cxt [] p used q is 

findValid' cxt env p used q (i:is) 
  = do (e, (x, px)) <- instanceToLogic i
       if isValid cxt env p q 
         then return $ Just used 
         else findValid' cxt (env ++ e) (F.pAnd [p, px]) (i:used) q is 
findValid' _ _ _ _ _ _ = return Nothing

isValid :: Context -> [(Symbol, F.Sort)] -> F.Pred -> F.Pred -> Bool
isValid cxt env p q = unsafePerformIO (checkValidWithContext  cxt env p q)

instanceToLogic :: Instance -> Pr ([(F.Symbol, F.Sort)], (F.Symbol, F.Pred))
instanceToLogic i@(Inst (f, xs, es))
  = do t  <- lookup (F.symbol f) . ae_sigs <$> get  
       sigs  <- ae_sigs <$> get  
       pp <- mapM rargToLogic es
       asubst' t (resultType $ varType f) pp  
       
rargToLogic :: TemplateArgument -> Pr ([(F.Symbol, F.Sort)], (F.Symbol, F.Pred))
rargToLogic (TA _ _ i) = targToLogic i 

targToLogic :: TArg -> Pr ([(F.Symbol, F.Sort)], (F.Symbol, F.Pred))
targToLogic (TDone e) 
  = do (ps, (z, t)) <- coreExprToLogic e
       let (en, (x, p)) = ([(x, s) | (x, s, _)<- ps] , (z, F.pAnd $ (map (\(_, _, p) -> p) ps)))
       return (en, (x, p))
targToLogic (THole)
  = error "targToLogic on Hole"
targToLogic (TTmp f es)
  = do t  <- lookup (F.symbol f) . ae_sigs <$> get
       pp <- mapM rargToLogic es
       asubst' t (resultType $ varType f) pp 

asubst' :: Maybe SpecType -> Type -> [([(F.Symbol, F.Sort)], (F.Symbol, F.Pred))] -> Pr ([(F.Symbol, F.Sort)], (F.Symbol, F.Pred))
asubst' Nothing ht pp
  = do let ss = concatMap fst pp 
       x <- freshSymbol 
       tce <- ae_emb <$> get 
       return ((x,typeSort tce ht):ss, (x, F.PTrue))

asubst' (Just t) ht es 
  = do let t' = go t 
       let ss = concatMap fst es 
       (x, p) <- mysub t' $ (map (fst . snd) es)
       tce <- ae_emb <$> get 
       return ((x, typeSort tce ht):ss, (x, (F.pAnd (p:(map (snd . snd) es)) )))
  where
    t' = go t 

    go (RAllT _ t) = go t
    go (RAllP _ t) = go t
    go t           = t 


mysub t xs = case stripRTypeBase t' of 
              Nothing -> (,F.PTrue) <$> freshSymbol
              Just t  -> do let (F.Reft (vv, pp)) = F.toReft t
                            x <- freshSymbol
                            let su = (vv, F.EVar x): zipWith (\y e -> (y, F.EVar e)) xs' xs
                            return (x, F.subst (F.mkSubst su) pp)
  where rep = toRTypeRep t 
        t' = (F.mkSubst (zipWith (\x y -> (x, F.EVar y)) (ty_binds rep) (xs))) `F.subst` (ty_res rep)
        xs' =  snd <$> (dropWhile (isClassType . fst) $ zip (ty_args rep) (ty_binds rep))



asubst acc (RAllT _ t) es = asubst acc t es 
asubst acc (RAllP _ t) es = asubst acc t es
asubst acc (RFun _ tx t _) es | isClassType tx = asubst acc t es 
asubst acc (RFun x tx t _) ((y, p):es) = asubst ((y,p):acc) (F.subst1 t (x, F.EVar y)) es 
asubst acc t               []          = case stripRTypeBase t of 
                                          Just x -> let (F.Reft (xx, pp)) = F.toReft x in (xx,pp):acc
                                          Nothing -> acc 
asubst _ t x = error ("asubst with " ++ show (t, x))

alogicType (RAllT _ t) = alogicType t
alogicType (RAllP _ t) = alogicType t
alogicType t           = t 


typeToReft :: Maybe SpecType -> Pr (F.Symbol, F.Pred)
typeToReft Nothing 
  = (, F.PTrue) <$> freshSymbol

typeToReft (Just t')
  = case stripRTypeBase t of 
      Nothing -> (, F.PTrue) <$> freshSymbol
      Just g -> do x <- freshSymbol
                   let (F.Reft (v, p)) = F.toReft g
                   return (x, F.subst1 p (v, F.EVar x))
  where t = simpl t'
        simpl (RAllP _ t) = simpl t
        simpl (RAllT _ t) = simpl t 
        simpl t           = t 


coreExprToLogic :: CoreExpr -> Pr ([(F.Symbol, F.Sort, F.Pred)], (Symbol, Maybe SpecType))
coreExprToLogic ee@(Var v) | isBaseTy $ varType v 
  = do t <- lookup (F.symbol v) . ae_sigs <$> get  
       tce <- ae_emb <$> get 
       (x, p) <- typeToReft t 
       return ([(x, typeSort tce $ varType v, F.pAnd [p, F.PAtom F.Eq (F.EVar $ F.symbol v) (F.EVar x)] )], (x, t))

coreExprToLogic ee@(Var v) 
  = do t <- lookup (F.symbol v) . ae_sigs <$> get  
       tce <- ae_emb <$> get 
       (x, p) <- typeToReft t 
       return ([(x, typeSort tce $ varType v, p)], (x, t))

coreExprToLogic ee@(App f e)
  = do (e1, (y, _)) <- coreExprToLogic e 
       (e2, (_, Just (RFun x tx t _))) <- mkFun <$> coreExprToLogic f 
       tce <- ae_emb <$> get 
       (z, pz) <- typeToReft (Just $ F.subst1 t (x, F.EVar y))
       return ((z, rTypeSort tce t, pz):(e1 ++ e2), (z, Just $ F.subst1 t (x, F.EVar y)))

mkFun (e, (x, Just t)) = (e, (x, Just $ go t))
  where 
    go (RAllT _ t) = go t
    go (RAllP _ t) = go t
    go t           = t 



freshSymbol 
  = tempSymbol "axiom_" <$> getUniq       


app e [] = e 
app e (x:xs) = app (App e x) xs 

rargToCoreExpr (TA _ _ targ) = go targ 
  where 
    go (TDone e)   = e
    go THole       = error "rargToCoreExpr: THole"
    go (TTmp f es) = app (Var f) (rargToCoreExpr <$> es)








-- |  Knowledge: things in scope that return a Proof. 
-- | TODO: Be careful to only apply inductive hypothesis on less things.

-- type Knowledge = [CoreExpr]

newtype Instance = Inst (Var, [Var], [TemplateArgument])

data TemplateArgument = TA {ta_type :: Type, ta_id :: Int, ta_instance :: TArg}

data TArg = TDone CoreExpr | TTmp Var [TemplateArgument] | THole

class HasHoles a where
  hasHoles :: a -> Bool 

instance HasHoles Instance where
  hasHoles (Inst (_, _, ts)) = any hasHoles ts 

instance HasHoles TemplateArgument where
  hasHoles (TA _ _ t) = hasHoles t 

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
  show (TA t i tmp) = "\n \t\t\t\tType = " ++ showPpr t ++ 
                      "\n \t\t\t\t\\tId = " ++ show i   ++ 
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


runStep :: Integer -> [Var] -> [Instance] -> Pr [Instance]
runStep iter cds is 
  = return $ go 0 [] argExprs  
  where
    go i acc _ | i == (fromInteger iter) = acc
    go i acc as   = go (i+1) (acc ++ concatMap (instantiateIst as) is) (makeNewArgs argTypes as)
    argTypes = validArgumentTypes is cs 
    argExprs = basicExprs argTypes bs

    (cs, bs) = L.partition (isFunctionType . varType) cds
--     inst1 = concatMap (instantiateIst argExprs)is 

makeNewArgs :: [([Var], Type, [Var])] -> [(([Var], Type), [CoreExpr])] -> [(([Var], Type), [CoreExpr])]
makeNewArgs ts as = [((avs, t), concatMap (instantiateConst as) vs) | (avs, t, vs) <- ts]  
                          


isFunctionType (FunTy _ _)    = True
isFunctionType (ForAllTy _ t) = isFunctionType t 
isFunctionType _              = False  

instantiateConst :: [(([Var], Type), [CoreExpr])] -> Var -> [CoreExpr]
instantiateConst aes v = if any null ess then [] else mkApp <$> go [] (reverse $ ess)
    where
      ess = (\ti -> (snd $ head $ filter (\((_, te), e) -> isInstanceOf (fv $ varType v) ti te) aes)) <$> (argumentTypes $ varType v)

      go acc (es:ess) = go (combine acc es) ess 
      go acc []       = acc 

      mkApp es = foldl App (Var v) es

      fv (ForAllTy v t) = v : fv t 
      fv _ = []

      combine [] es      = map (\e -> [e]) es  
      combine acc []     = []
      combine acc (e:es) = (map (e:) acc) ++ combine acc es




instantiateIst :: [(([Var], Type), [CoreExpr])] -> Instance -> [Instance]
instantiateIst aes i@(Inst (a, tvs, as)) = if any null ess then [] else (((\ts -> Inst (a, tvs, ts)) <$> (go [] (reverse ess) (reverse as))))
    where
      ess = (\ti -> (snd $ head $ filter (\((tvs', te), e) -> isInstanceOf (tvs' ++ tvs) ti te) aes)) <$> (ta_type <$> as)



      go acc (es:ess) ((TA ti ii _):ts) = go (combine ti ii acc es)  ess ts 
      go acc []       []                = acc 

      combine ti ii [] es      = map (\e -> [TA ti ii (TDone e)]) es  
      combine ti ii acc []     = []
      combine ti ii acc (e:es) = (map (((TA ti ii (TDone e))):) acc) ++ combine ti ii acc es


{-


runStep :: Integer -> [Var] -> [Instance] -> Pr [Instance]
runStep iter cds is 
  = return $ go 1 [] is 
  where
    go i acc is | i == (fromInteger iter) = acc
    go i acc is = let (h, noh) = traceShow ("\n\nVARS = \n" ++ show cds ++ "\n\nSTEP " ++ show i ++ "\n\n"
                                            ++ "\n\nARGUMENT TYPES\n\n" ++ show argTypes ++ "\n\n"
                                            ++ "\n\nARGUMENT EXPRESSIONS\n\n" ++ show argExprs ++ "\n\n"
                                            ++ "\n\nINSTANTIATE ONCE\n\n"     ++ show inst1 ++ "\n\n"
                                            ++ "\n\nINSTANTIATE TWICE\n\n"     ++ show inst2 ++ "\n\n"
                                           ) $ 
                                     L.partition hasHoles is in 
                  let is'      = runStepOne i cds h in 
                  go (i+1) (acc ++ noh) is' 
    argTypes = validArgumentTypes is 
    argExprs = validExprs argTypes cds
    inst1 = instantiate3 argExprs <$> is 
    inst2 = ['c'] 

instantiate3 :: [(([Var], Type), [CoreExpr])] -> Instance -> [CoreExpr]
instantiate3 aes (Inst (a, tvs, [])) = [Var a] 
instantiate3 aes (Inst (a, tvs, [(TA t _ _)]))
   = App (Var a) <$> (snd $ head $ filter (\((_, te), e) -> isInstanceOf tvs t te) aes) 
instantiate3 aes (Inst (a, tvs, [(TA t1 _ _), (TA t2 _ _)]))
   = [App (App (Var a) a1) a2 | a1 <- e1, a2 <- e2]
   where 
    e1 = (snd $ head $ filter (\((_, te), e) -> isInstanceOf tvs t1 te) aes) 
    e2 = (snd $ head $ filter (\((_, te), e) -> isInstanceOf tvs t2 te) aes) 
instantiate3 aes (Inst (a, tvs, [(TA t1 _ _), (TA t2 _ _), (TA t3 _ _)]))
   = [App (App (App (Var a) a1) a2) a3 | a1 <- e1, a2 <- e2, a3 <- e3]
   where 
    e1 = (snd $ head $ filter (\((_, te), e) -> isInstanceOf tvs t1 te) aes) 
    e2 = (snd $ head $ filter (\((_, te), e) -> isInstanceOf tvs t2 te) aes) 
    e3 = (snd $ head $ filter (\((_, te), e) -> isInstanceOf tvs t3 te) aes) 
instantiate3 aes (Inst (a, tvs, xs)) = [] 
-}

basicExprs :: [([Var], Type, [Var])] -> [Var] -> [(([Var], Type), [CoreExpr])]
basicExprs vts cds = go <$> vts
  where
    go (vs, t, _) = ((vs, t), Var <$> filter (isInstanceOf vs t . varType) cds)


validArgumentTypes :: [Instance] -> [Var] -> [([Var], Type, [Var])]
validArgumentTypes is cs = addConstructors <$> (combineTypes [] $ (concatMap go is ++ concatMap go' cs) )
  where 
    go (Inst(ax, vs, tas)) = (vs,) <$> (ta_type <$> tas) 
    go' v                  = [(fv $ varType v, t) | t <- argumentTypes $ varType v]
    combineTypes acc []       = acc
    combineTypes acc ((vs, t):ts)   
       | any (isInstanceOf vs t . snd) acc = combineTypes acc ts
       | otherwise                         = combineTypes ((vs,t):acc) ts
    addConstructors (vs, t) = (vs, t, [c | c <- cs, isInstanceOf vs t $ resultType $ varType c])

    fv (ForAllTy v t) = v:fv t
    fv t = [] 


instance Show Type where
  show = showPpr 

-- Then split ready and runStep for the rest
runStepOne :: Int -> [Var] -> [Instance] -> [Instance]
runStepOne i cds is =  concatMap go is
  where
    go (Inst (ax, vs, targs)) = [Inst (ax, vs, tas) | tas <- expandOneHole 0 vs cds targs] 

{-
append
C

N, 

-}
{-
runStep :: Integer -> [Var] -> [Instance] -> [Instance]
runStep iter cds is = go 1 [] is 
  where
    go i acc is | i == (fromInteger iter) = acc
    go i acc is = let (h, noh) = traceShow ("\n\nSTEP " ++ show i ++ "\n\n") $ L.partition hasHoles is in 
                  let is'      = runStepOne i cds h in 
                  go (i+1) (acc ++ noh) is' 


-- Then split ready and runStep for the rest
runStepOne :: Int -> [Var] -> [Instance] -> [Instance]
runStepOne i cds is =  concatMap go is
  where
    go (Inst (ax, vs, targs)) = [Inst (ax, vs, tas) | tas <- expandOneHole 0 vs cds targs] 
-}

expandHole :: [Var] -> [Var] -> TemplateArgument -> [TemplateArgument]
expandHole tvs cds (TA t i THole)       = TA t i <$> instantiateHole tvs cds t 
expandHole tvs cds (TA t i (TDone e))   = [TA t i $ TDone e]
expandHole tvs cds (TA t i (TTmp v ts)) = (\ts' -> TA t i (TTmp v ts')) <$> expandOneHole 1 tvs cds ts 


expandOneHole :: Int -> [Var] -> [Var] -> [TemplateArgument] -> [[TemplateArgument]]
expandOneHole n tvs cds ts = go [] ts 
  where
    go acc [] 
      = [reverse acc]
    go acc (TA t i THole:tas)      
      = map (\ta -> (reverse acc) ++ [TA t i ta] ++ tas) (instantiateHole tvs cds t)
    go acc (TA t i (TDone e):tas)   
      = go (TA t i (TDone e):acc) tas
    go acc (TA t i (TTmp v tts):tas) | n < 2 -- hole nesting 
      = map (\xs -> (reverse acc) ++ [TA t i (TTmp v xs)] ++ tas) (expandOneHole (n+1) (L.nub (forallTyVars (varType v) ++ tvs)) cds tts)
    go acc (TA t i (TTmp v tts):tas)  
      = []

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

makeTemplate t = TA t (-1) THole

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