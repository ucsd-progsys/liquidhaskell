{-# LANGUAGE EmptyDataDecls       #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE OverloadedStrings    #-}

-- Defunctionalization of higher order logic 

module Language.Fixpoint.Solver.Defunctionalize (defunctionalize) where

import           Language.Fixpoint.Misc            (secondM, errorstar, traceShow)
import           Language.Fixpoint.Solver.Validate (symbolSorts)
import           Language.Fixpoint.Types hiding    (allowHO)
import           Language.Fixpoint.Types.Config hiding (eliminate)
import           Language.Fixpoint.SortCheck       
import           Language.Fixpoint.Types.Visitor   (mapExpr, lamSize)

import qualified Language.Fixpoint.Smt.Theories as Thy
import           Control.Monad.State
import qualified Data.HashMap.Strict as M
import           Data.Hashable

defunctionalize :: (Fixpoint a) => Config -> SInfo a -> SInfo a 
defunctionalize cfg si = evalState (defunc "INIT." si) (makeInitDFState cfg si)


class Defunc a where
  defunc :: String -> a -> DF a 

-------------------------------------------------------------------------------
--------  Sort defunctionalization --------------------------------------------
-------------------------------------------------------------------------------

instance Defunc Sort where
  defunc _ s = defuncSort s 

defuncSort s = do   
  hoFlag <- dfHO <$> get
  return $ if hoFlag then go s else s 
  where
    go (FAbs i s)    = FAbs i $ go s 
    go (FFunc s1 s2) = funSort (go s1) (go s2)
    go (FApp s1 s2)  = FApp    (go s1) (go s2)  
    go s             = s 

funSort :: Sort -> Sort -> Sort 
funSort s1 s2 = FApp (FApp funcSort s1) s2 

-------------------------------------------------------------------------------
--------  Expressions defunctionalization -------------------------------------
-------------------------------------------------------------------------------

instance Defunc Expr where
  defunc str e = do env    <- dfenv <$> get 
                    hoFlag <- dfHO  <$> get
                    exFlag <- f_ext <$> get  
                    tx hoFlag exFlag $ elaborate env  (traceShow ("toelaborate " ++ str) e)
   where 
     tx hoFlag exFlag e
       | exFlag && hoFlag
       = defuncExpr (txExtensionality (txnumOverloading e))
       | hoFlag 
       = defuncExpr (txnumOverloading e)
       | otherwise 
       = return     (txnumOverloading e)


defuncExpr :: Expr -> DF Expr
defuncExpr = go
  where
    go e@(ESym _)       = return e
    go e@(ECon _)       = return e
    go e@(EVar _)       = return e
    go e@(PKVar _ _)    = return e 
    go e@(EApp e1 e2)   = logRedex e >> defuncEApp e1 e2 
    go (ENeg e)         = ENeg <$> go e
    go (EBin o e1 e2)   = EBin o <$> go e1 <*> go e2
    go (EIte e1 e2 e3)  = EIte <$> go e1 <*> go e2 <*> go e3 
    go (ECst e t)       = (`ECst` t) <$> go e
    go (PTrue)          = return PTrue
    go (PFalse)         = return PFalse
    go (PAnd [])        = return PTrue
    go (PAnd ps)        = PAnd <$> mapM go ps
    go (POr [])         = return PFalse
    go (POr ps)         = POr <$> mapM go ps
    go (PNot p)         = PNot <$> go  p
    go (PImp p q)       = PImp <$> go p <*> go q
    go (PIff p q)       = PIff <$> go p <*> go q
    go (PExist bs p)    = do bs' <- mapM (defunc "PExist") bs
                             p'  <- withExtendedEnv bs $ go p
                             return $ PExist bs' p'
    go (PAll   bs p)    = do bs' <- mapM (defunc "PAll") bs
                             p'  <- withExtendedEnv bs $ go p
                             return $ PAll bs' p'
    go (PAtom r e1 e2)  = PAtom r <$> go e1 <*> go e2 
    go PGrad            = return PGrad
    go (ELam x ex)      = defuncELam x ex
    go  e               = errorstar ("defunc Pred: " ++ show e)



defuncELam :: (Symbol, Sort) -> Expr -> DF Expr 
defuncELam (x, s) e 
  | i <= maxLamArg
  = do de <- defuncExpr $ subst1 e (x, EVar x')
       logLam $ ELam (x', s) $ de
  | otherwise
  = errorstar "TOO MANY LAMBDAS"
  where
    x' = makeLamArg s i  
    i  = (fromEnum $ lamSize e) + 1

maxLamArg :: Int 
maxLamArg = 7

-- NIKI TODO: allow non integer lambda arguments
-- sorts = [setSort intSort, bitVecSort intSort, mapSort intSort intSort, boolSort, realSort, intSort]
makeLamArg :: Sort -> Int  -> Symbol
makeLamArg _ i = intArgName i


defuncEApp :: Expr -> Expr -> DF Expr
defuncEApp e1 e2 
  | Thy.isSmt2App (eliminate f) es 
  = eApps f <$> mapM defuncExpr es 
  | otherwise
  = makeApplication <$> defuncExpr e1 <*> defuncExpr e2
  where
    (f, es) = splitArgs $ EApp e1 e2 



-- e1 e2 => App (App runFun e1) (toInt e2) 

makeApplication :: Expr -> Expr -> Expr
makeApplication e1 e2 = ECst (EApp (EApp (EVar f) e1') (toInt e2')) s
  where
    f   = makeFunSymbol $ specify s 
    s   = resultType e1 
    e1' = e1 
    e2' = e2 

specify :: Sort -> Sort 
specify (FAbs _ s) = specify s
specify s          = s 

resultType :: Expr -> Sort
resultType e = go $ exprSort e 
  where
    go (FAbs i s)               = FAbs i $ go s 
    go (FFunc (FFunc s1 s2) sx) = FFunc (go (FFunc s1 s2)) sx
    go (FFunc _ sx)             = sx
    go sj          = errorstar ("makeFunSymbol on non Fun " ++ show (e, sj))


makeFunSymbol :: Sort -> Symbol
makeFunSymbol s 
  | (FApp (FTC c) _)          <- s, fTyconSymbol c == "Set_Set"
  = setApplyName 1
  | (FApp (FApp (FTC c) _) _) <- s, fTyconSymbol c == "Map_t"
  = mapApplyName 1
  | (FApp (FTC bv) (FTC s))   <- s, Thy.isBv bv, Just _ <- Thy.sizeBv s
  = bitVecApplyName 1
  | FTC c                     <- s, c == boolFTyCon
  = boolApplyName 1
  | s == FReal
  = realApplyName 1
  | otherwise
  = intApplyName 1



toInt :: Expr -> Expr
toInt e
  |  (FApp (FTC c) _)         <- s, fTyconSymbol c == "Set_Set"
  = castWith setToIntName e
  | (FApp (FApp (FTC c) _) _) <- s, fTyconSymbol c == "Map_t"
  = castWith mapToIntName e
  | (FApp (FTC bv) (FTC s))   <- s, Thy.isBv bv, Just _ <- Thy.sizeBv s
  = castWith bitVecToIntName e
  | FTC c                     <- s, c == boolFTyCon
  = castWith boolToIntName e
  | FTC c                     <- s, c == realFTyCon
  = castWith realToIntName e
  | otherwise
  = e
  where
    s = exprSort e

castWith :: Symbol -> Expr -> Expr
castWith s = EApp (EVar s)

eliminate :: Expr -> Expr
eliminate = mapExpr go 
  where
    go (ECst e _) = e 
    go e          = e 

splitArgs :: Expr -> (Expr, [Expr])
splitArgs = go [] 
  where
    go acc (EApp e1 e) = go (e:acc) e1 
    go acc (ECst e _)  = go acc e 
    go acc e           = (e, acc)



makeAxioms :: DF [Expr]
makeAxioms = do 
  alphaFlag <- a_eq <$> get 
  betaFlag  <- b_eq <$> get 
  asa <- if alphaFlag then makeAlphaAxioms else return [] 
  asb <- if betaFlag  then withNoEquivalence (makeBetaAxioms >>= mapM (defuncExpr)) else return []
  return (asa ++ asb)


-------------------------------------------------------------------------------
--------  Alpha Equivalence  --------------------------------------------------
-------------------------------------------------------------------------------

logLam :: Expr -> DF Expr 
logLam e@(ELam _ _) 
  = do aEq <- a_eq <$> get 
       if aEq then modify $ \s -> s{dfLams = traceShow ("alpha logged " ++ showpp (eliminate e)) e:dfLams s} else return ()
       return e 
logLam e            
  = return e 

makeAlphaAxioms :: DF [Expr]
makeAlphaAxioms = do 
  lams <- dfLams <$> get 
  return $ concatMap makeAlphaEq lams

makeAlphaEq :: Expr -> [Expr]
makeAlphaEq ee@(ELam (x, s) e)
  = [makeEq (normalizeLams ee) ee' 
     | (i, ee') <- map (\j -> normalizeLamsFromTo j (ELam (x, s) e)) [1..maxLamArg-1]
     , i <= maxLamArg ]
makeAlphaEq _ 
  = [] 

normalizeLams :: Expr -> Expr
normalizeLams e = snd $ normalizeLamsFromTo 1 e

normalizeLamsFromTo :: Int ->  Expr -> (Int, Expr)
normalizeLamsFromTo i e = go e
  where
    go (ELam (y, sy) e) = let (i', e') = go e
                              y'      = makeLamArg sy i'
                          in (i'+1, ELam (y', sy) (e' `subst1` (y, EVar y')))
    go (EApp e1 e2)     = let (i1, e1') = go e1
                              (i2, e2') = go e2
                          in (max i1 i2, EApp e1' e2')
    go (ECst e s)       = mapSnd (`ECst` s) (go e)
    go e                = (i, e)

    mapSnd f (x, y) = (x, f y)
-------------------------------------------------------------------------------
--------  Beta Equivalence  ---------------------------------------------------
-------------------------------------------------------------------------------

logRedex :: Expr -> DF ()
logRedex e@(EApp f _) 
  | (ELam _ _) <- eliminate f
  = do bEq <- b_eq <$> get 
       if bEq then modify $ \s -> s{dfRedex = ( traceShow ("REDEX LOGGED " ++ showpp (eliminate e)) e):dfRedex s} else return ()
logRedex _
  = return ()

makeBetaAxioms :: DF [Expr]
makeBetaAxioms = do 
  red <- dfRedex <$> get 
  return $ (makeBetaEq <$> red)

makeBetaEq :: Expr -> Expr
makeBetaEq e@(EApp f ex)
  | ELam (x, _) bd <- unECst f
  = makeEq e (bd `subst1` (x, ex))
  where
    unECst (ECst e _) = unECst e 
    unECst e          = e 
makeBetaEq _ 
  = PTop

makeEq :: Expr -> Expr -> Expr
makeEq e1 e2
  | e1 == e2  = PTrue
  | otherwise = EEq e1 e2

-------------------------------------------------------------------------------
--------  Numeric Overloading  ------------------------------------------------
-------------------------------------------------------------------------------

txnumOverloading :: Expr -> Expr 
txnumOverloading = mapExpr go 
  where
    go (ETimes e1 e2)
      | exprSort e1 == FReal, exprSort e2 == FReal
      = ERTimes e1 e2  
    go (EDiv   e1 e2)
      | exprSort e1 == FReal, exprSort e2 == FReal
      = ERDiv   e1 e2 
    go e 
      = e 


-------------------------------------------------------------------------------
--------  Extensionality  -----------------------------------------------------
-------------------------------------------------------------------------------

txExtensionality :: Expr -> Expr
txExtensionality = mapExpr go 
  where
    go (EEq e1 e2)
      | FFunc _ _ <- exprSort e1, FFunc _ _ <- exprSort e2
      = mkExFunEq e1 e2 
    go e 
      = e 

mkExFunEq :: Expr -> Expr -> Expr 
mkExFunEq e1 e2 = PAnd [PAll (zip xs ss)
                             (EEq
                                (ECst (eApps e1' es) s)
                                (ECst (eApps e2' es) s))
                       , EEq e1 e2]
  where
    es      = zipWith (\x s -> ECst (EVar x) s) xs ss
    xs      = (\i -> symbol ("local_fun_arg" ++ show i)) <$> [1..length ss]
    (s, ss) = splitFun [] s1 
    s1      = exprSort e1

    splitFun acc (FFunc s ss) = splitFun (s:acc) ss
    splitFun acc s            = (s, reverse acc)

    e1' = ECst e1 s1 
    e2' = ECst e2 s1 


-------------------------------------------------------------------------------
--------  Expressions sort  ---------------------------------------------------
-------------------------------------------------------------------------------
exprSort :: Expr -> Sort 
exprSort (ECst _ s)      
  = s 
exprSort (ELam (_,sx) e) 
  = FFunc sx $ exprSort e
exprSort (EApp e ex) | FFunc sx s <- gen $ exprSort e
  = maybe s (`apply` s) $ unifySorts (exprSort ex) sx
  where
    gen (FAbs _ t) = gen t
    gen t          = t  
exprSort e
  = errorstar ("\nexprSort on unexpected expressions" ++ show e)

-------------------------------------------------------------------------------
--------  Containers defunctionalization --------------------------------------
-------------------------------------------------------------------------------

instance (Defunc (c a), TaggedC c a) => Defunc (GInfo c a) where
  defunc str fi = do cm'    <- defunc (str ++ "cm.") $ cm    fi 
                     ws'    <- defunc (str ++ "ws.") $ ws    fi 
                     setBinds $ mconcat ((senv <$> (M.elems $ cm fi)) ++ (wenv <$> (M.elems $ ws fi)))
                     gLits' <- defunc (str ++ "gl.") $ gLits fi 
                     dLits' <- defunc (str ++ "gll.") $ dLits fi 
                     bs'    <- defunc (str ++ "bs.") $ bs    fi 
                     quals' <- defunc (str ++ "qs.") $ quals fi 
                     axioms <- makeAxioms  
                     return $ fi { cm      = cm'
                                 , ws      = ws'
                                 , gLits   = gLits'
                                 , dLits   = dLits'
                                 , bs      = bs'
                                 , quals   = quals' 
                                 , asserts = axioms
                                 }

instance Defunc (SimpC a) where
  defunc str sc = do crhs' <- defunc (str ++ "simplC.")$ _crhs sc 
                     return $ sc {_crhs = crhs'}
 
instance Defunc (WfC a)   where
  defunc str wf = do wrft' <- defunc (str ++ "wfc.") $ wrft wf
                     return $ wf {wrft = wrft'}

instance Defunc Qualifier where
  defunc str q = do qParams' <- defunc (str ++ "qp.") $ qParams q 
                    withExtendedEnv (qParams q) $ withNoEquivalence $ do 
                     qBody'   <- defunc (str ++ "qbdof . " ++ show ( q)) $ qBody   q
                     return    $ q {qParams = qParams', qBody = qBody'}

instance Defunc SortedReft where
  defunc str (RR s r) = RR <$> defunc (str ++ "sr.") s <*> defunc (str ++ "sref.") r 

instance Defunc (Symbol, SortedReft) where
  defunc str (x, (RR s (Reft (v, e)))) 
    = (x,) <$> defunc (str ++ "ssr.") (RR s (Reft (x, subst1 e (v, EVar x)))) 

instance Defunc Reft where
  defunc str (Reft (x, e)) = Reft . (x,) <$> defunc (str ++ "reft.") e 

instance Defunc (a, Sort, c) where
  defunc str (x, y, z) = (x, , z) <$> defunc (str ++ "triple.") y 

instance Defunc (a, Sort) where
  defunc str (x, y) = (x, ) <$> defunc (str ++ "pair.") y 

instance Defunc a => Defunc (SEnv a) where
  defunc str = mapMSEnv (defunc (str ++ "senv."))

instance Defunc BindEnv   where
  defunc str bs = do dfbs <- dfbenv <$> get
                     let f (i, xs) = if i `memberIBindEnv` dfbs 
                                       then  (i,) <$> defunc (str ++ "bindenv.") xs 
                                       else  (i,) <$> matchSort xs
                     mapWithKeyMBindEnv f bs 
   where
    -- The refinement cannot be elaborated thus defunc-ed because
    -- the bind does not appear in any contraint, 
    -- thus unique binders does not perform properly
    -- The sort should be defunc, to ensure same sort on double binders 
    matchSort (x, RR s r) = ((x,) . (`RR` r)) <$> defunc "matchSort." s

instance Defunc a => Defunc [a] where
  defunc str = mapM (defunc (str ++ "list.") )

instance (Defunc a, Eq k, Hashable k) => Defunc (M.HashMap k a) where
  defunc str m = M.fromList <$> mapM (secondM (defunc (str ++ "map."))) (M.toList m) 

type DF    = State DFST

type DFEnv = SEnv Sort

data DFST
  = DFST { fresh   :: !Int 
         , dfenv   :: !DFEnv
         , dfbenv  :: !IBindEnv
         , f_ext   :: !Bool   -- enable extensionality axioms
         , a_eq    :: !Bool   -- enable alpha equivalence axioms
         , b_eq    :: !Bool   -- enable beta equivalence axioms
         , f_norm  :: !Bool   -- enable normal form axioms
         , dfHO    :: !Bool   -- allow higher order thus defunctionalize
         , dfLams  :: ![Expr] -- lambda expressions appearing in the expressions
         , dfRedex :: ![Expr] -- redexes appearing in the expressions
         }

makeInitDFState :: Config -> SInfo a -> DFST
makeInitDFState cfg si 
  = DFST { fresh   = 0 
         , dfenv   = fromListSEnv xs
         , dfbenv  = mempty 
         , f_ext   = extensionality   cfg
         , a_eq    = alphaEquivalence cfg 
         , b_eq    = betaEquivalence  cfg 
         , f_norm  = normalForm       cfg  
         , dfHO    = allowHO          cfg 
         , dfLams  = [] 
         , dfRedex = []
         }
  where
    xs = symbolSorts cfg si ++ concat [ [(x,s), (y,s)] | (_, x, RR s (Reft (y, _))) <- bindEnvToList $ bs si]


setBinds :: IBindEnv -> DF ()
setBinds e = modify $ \s -> s{dfbenv = e}

withExtendedEnv ::  [(Symbol, Sort)] -> DF a -> DF a
withExtendedEnv bs act = do
  env <- dfenv <$> get
  let env' = foldl (\env (x, t) -> insertSEnv x t env) env bs
  modify $ \s -> s{dfenv = env'}
  r <- act
  modify $ \s -> s{dfenv = env}
  return r


withNoEquivalence :: DF a -> DF a
withNoEquivalence act = do
  aEq <- a_eq <$> get
  bEq <- b_eq <$> get
  modify $ \s -> s{a_eq = False, b_eq = False}
  r <- act
  modify $ \s -> s{a_eq = aEq,   b_eq = bEq}
  return r


{- 

withNoExtensionality :: DF a -> DF a
withNoExtensionality act = do 
  extFlag <- f_ext <$> get 
  modify $ \s -> s{f_ext = False}
  x <- act
  modify $ \s -> s{f_ext = extFlag}
  return x 


freshSym :: DF Symbol
freshSym = do
  n  <- fresh <$> get
  modify $ \s -> s{fresh = n + 1}
  return $ intSymbol "lambda_fun_" n

-}
