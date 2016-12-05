{-# LANGUAGE EmptyDataDecls       #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE OverloadedStrings    #-}

-- Defunctionalization of higher order logic

module Language.Fixpoint.Defunctionalize.Defunctionalize (defunctionalize) where

import           Language.Fixpoint.Misc            (secondM, errorstar, mapSnd)
import           Language.Fixpoint.Solver.Validate (symbolSorts)
import           Language.Fixpoint.Types        hiding (allowHO)
import           Language.Fixpoint.Types.Config hiding (eliminate)
import           Language.Fixpoint.SortCheck
import           Language.Fixpoint.Types.Visitor   (mapExpr, mapMExpr)

import qualified Language.Fixpoint.Smt.Theories as Thy
import           Control.Monad.State
import qualified Data.HashMap.Strict as M
import           Data.Hashable
import qualified Data.List           as L

import qualified Data.Text                 as T

defunctionalize :: (Fixpoint a) => Config -> SInfo a -> SInfo a
defunctionalize cfg si = evalState (defunc si) (makeInitDFState cfg si)


class Defunc a where
  defunc :: a -> DF a

-------------------------------------------------------------------------------
--------  Sort defunctionalization --------------------------------------------
-------------------------------------------------------------------------------

instance Defunc Sort where
  defunc s = defuncSort s

defuncSort :: Sort -> DF Sort
defuncSort s = do
  hoFlag <- dfHO <$> get
  return $ if hoFlag then go s else s
  where
    go s | isString s = strSort
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
  defunc = txExpr True



txCastedExpr :: Expr -> DF Expr
txCastedExpr = txExpr False

txExpr :: Bool -> Expr -> DF Expr
txExpr b e = do env    <- dfenv <$> get
                hoFlag <- dfHO  <$> get
                exFlag <- f_ext <$> get
                stFlag <- dfStr <$> get
                tx stFlag hoFlag exFlag $ if b then elaborate env e else e
   where
     tx stFlag hoFlag exFlag e
       | exFlag && hoFlag
       = (txExtensionality . txnumOverloading <$> (txStr stFlag $ e)) >>= defuncExpr
       | hoFlag
       = (txnumOverloading <$> (txStr stFlag $ e)) >>= defuncExpr
       | otherwise
       = txnumOverloading <$> (txStr stFlag $ e)


defuncExpr :: Expr -> DF Expr
defuncExpr e = writeLog ("DEFUNC EXPR " ++ showpp (eliminate e)) >> go Nothing e
  where
    go _ e@(ESym _)       = return e
    go _ e@(ECon _)       = return e
    go _ e@(EVar _)       = return e
    go _ e@(PKVar _ _)    = return e
    go s e@(EApp e1 e2)   = logRedex e >> defuncEApp s e1 e2
    go s (ENeg e)         = ENeg <$> go s e
    go _ (EBin o e1 e2)   = EBin o <$> go Nothing e1 <*> go Nothing e2
    go s (EIte e1 e2 e3)  = EIte <$> go (Just boolSort) e1 <*> go s e2 <*> go s e3
    go _ (ECst e t)       = (`ECst` t) <$> go (Just t) e
    go _ (PTrue)          = return PTrue
    go _ (PFalse)         = return PFalse
    go _ (PAnd [])        = return PTrue
    go _ (PAnd ps)        = PAnd <$> mapM (go (Just boolSort)) ps
    go _ (POr [])         = return PFalse
    go _ (POr ps)         = POr <$> mapM (go (Just boolSort)) ps
    go _ (PNot p)         = PNot <$> go (Just boolSort) p
    go _ (PImp p q)       = PImp <$> go (Just boolSort) p <*> go (Just boolSort) q
    go _ (PIff p q)       = PIff <$> go (Just boolSort) p <*> go (Just boolSort) q
    go _ (PExist bs p)    = do bs' <- mapM defunc bs
                               p'  <- withExtendedEnv bs $ go (Just boolSort) p
                               return $ PExist bs' p'
    go _ (PAll   bs p)    = do bs' <- mapM defunc bs
                               p'  <- withExtendedEnv bs $ go (Just boolSort) p
                               return $ PAll bs' p'
    go _ (PAtom r e1 e2)  = PAtom r <$> go Nothing e1 <*> go Nothing e2
    go _ PGrad            = return PGrad
    go _ (ELam x ex)      = (df_lam <$> get) >>= defuncELam x ex
    go _ e                = errorstar ("defunc Pred: " ++ show e)



defuncELam :: (Symbol, Sort) -> Expr -> Bool -> DF Expr
defuncELam (x, s) e aeq | aeq
  = do y  <- freshSym
       de <- defuncExpr $ subst1 e (x, EVar y)
       logLam (y, s) (subst1 e (x, EVar y))
       return $ normalizeLams $ ELam (y, s) de
defuncELam xs e _
  = ELam xs <$> defuncExpr e


maxLamArg :: Int
maxLamArg = 7

-- NIKI TODO: allow non integer lambda arguments
-- sorts = [setSort intSort, bitVecSort intSort, mapSort intSort intSort, boolSort, realSort, intSort]
makeLamArg :: Sort -> Int  -> Symbol
makeLamArg _ i = intArgName i


defuncEApp :: Maybe Sort -> Expr -> Expr -> DF Expr
defuncEApp ms e1 e2
  | Thy.isSmt2App (eliminate f) es
  = eApps f <$> mapM defuncExpr es
  | otherwise
  = makeApplication ms <$> (dfLog <$> get) <*> defuncExpr e1 <*> defuncExpr e2
  where
    (f, es) = splitArgs $ EApp e1 e2


-- e1 e2 => App (App runFun e1) (toInt e2)
makeApplication :: Maybe Sort -> String -> Expr -> Expr -> Expr
makeApplication Nothing str e1 e2 = ECst (EApp (EApp (EVar f) e1') (toInt e2')) s
  where
    f   = makeFunSymbol $ specify s
    s   = resultType str e1 e2
    e1' = e1
    e2' = e2
makeApplication (Just s) _ e1 e2 = ECst (EApp (EApp (EVar f) e1') (toInt e2')) s
  where
    f   = makeFunSymbol $ specify s
    e1' = e1
    e2' = e2

specify :: Sort -> Sort
specify (FAbs _ s) = specify s
specify s          = s

resultType :: String -> Expr -> Expr -> Sort
resultType str e _ = go $ exprSort e
  where
    go (FAbs i s)               = FAbs i $ go s
    go (FFunc (FFunc s1 s2) sx) = FFunc (go (FFunc s1 s2)) sx
    go (FFunc _ sx)             = sx
    go sj          = errorstar (str ++ "\nmakeFunSymbol on non Fun " ++ showpp (eliminate e, sj) ++ "\nuneliminated\n" ++ showpp e)


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
  asyms     <- makeSymbolAxioms
  asb       <- if betaFlag  then withNoLambdaNormalization $ withNoEquivalence makeBetaAxioms   else return []
  asa       <- if alphaFlag then withNoLambdaNormalization $ withNoEquivalence makeAlphaAxioms  else return []
  return (asa ++ asb ++ asyms)

-------------------------------------------------------------------------------
------------  Symbols ---------------------------------------------------------
-------------------------------------------------------------------------------

logSym :: SymConst -> DF ()
logSym x = modify $ \s -> s{dfSyms = x:dfSyms s}

makeSymbolAxioms :: DF [Expr]
makeSymbolAxioms = ((map go . dfSyms) <$> get) >>= mapM txCastedExpr
  where
    go (SL s) = EEq (makeGenStringLen $ symbolExpr $ SL s) ((expr $ T.length s) `ECst` intSort)

symbolExpr :: SymConst -> Expr
symbolExpr = EVar . symbol

makeStringLen :: Expr -> Expr
makeStringLen = EApp (EVar Thy.strLen)

makeGenStringLen :: Expr -> Expr
makeGenStringLen e
 = EApp (ECst (EVar Thy.genLen) (FFunc strSort intSort)) (ECst e strSort)
   `ECst` intSort

-------------------------------------------------------------------------------
--------  Alpha Equivalence  --------------------------------------------------
-------------------------------------------------------------------------------

logLam :: (Symbol, Sort) -> Expr -> DF Expr
logLam xs bd
  = do aEq <- a_eq <$> get
       modify $ \s -> s{dfRedex = closeLams xs <$> dfRedex s}
       modify $ \s -> s{dfLams  = closeLams xs <$> dfLams s}
       if aEq
         then modify $ \s -> s{dfLams = e:dfLams s}
         else return ()
       return $ normalizeLams e
  where
    e = ELam xs bd
    closeLams (x, s) e = if x `elem` (syms e) then PAll [(x, s)] e else e

makeAlphaAxioms :: DF [Expr]
makeAlphaAxioms = do
  lams <- dfLams <$> get
  mapM defuncExpr $ concatMap makeAlphaEq $ L.nub (normalizeLams <$> lams)



makeAlphaEq :: Expr -> [Expr]
makeAlphaEq e = go e ++ go' e
  where
    go ee
      = makeEqForAll ee (normalize ee)
    go' ee@(ELam (x, s) e)
      = [makeEq ee ee'
         | (i, ee') <- map (\j -> normalizeLamsFromTo j (ELam (x, s) e)) [1..maxLamArg-1]
         , i <= maxLamArg ]
    go' _
      = []


-------------------------------------------------------------------------------
------------  Normalizations --------------------------------------------------
-------------------------------------------------------------------------------


-- head normal form

normalize :: Expr -> Expr
normalize = snd . go
  where
    go (ELam (y, sy) e) = let (i', e') = go e
                              y'      = makeLamArg sy i'
                          in (i'+1, ELam (y', sy) (e' `subst1` (y, EVar y')))
    go (EApp e e2)
      |  (ELam (x, _) bd) <- unECst e
                        = let (i1, e1') = go bd
                              (i2, e2') = go e2
                          in (max i1 i2, e1' `subst1` (x, e2'))
    go (EApp e1 e2)     = let (i1, e1') = go e1
                              (i2, e2') = go e2
                          in (max i1 i2, EApp e1' e2')
    go (ECst e s)       = mapSnd (`ECst` s) (go e)
    go (PAll bs e)      = mapSnd (PAll bs)  (go e)
    go e                = (1, e)

    unECst (ECst e _) = unECst e
    unECst e          = e

-- normalize lambda arguments

normalizeLams :: Expr -> Expr
normalizeLams e = snd $ normalizeLamsFromTo 1 e

normalizeLamsFromTo :: Int -> Expr -> (Int, Expr)
normalizeLamsFromTo i   = go
  where
    go (ELam (y, sy) e) = let (i', e') = go e
                              y'      = makeLamArg sy i'
                          in (i'+1, ELam (y', sy) (e' `subst1` (y, EVar y')))
    go (EApp e1 e2)     = let (i1, e1') = go e1
                              (i2, e2') = go e2
                          in (max i1 i2, EApp e1' e2')
    go (ECst e s)       = mapSnd (`ECst` s) (go e)
    go (PAll bs e)      = mapSnd (PAll bs) (go e)
    go e                = (i, e)

-------------------------------------------------------------------------------
--------  Beta Equivalence  ---------------------------------------------------
-------------------------------------------------------------------------------

logRedex :: Expr -> DF ()
logRedex e@(EApp f _)
  | (ELam _ _) <- eliminate f
  = do bEq <- b_eq <$> get
       if bEq then modify $ \s -> s{dfRedex = e:dfRedex s} else return ()
logRedex _
  = return ()

makeBetaAxioms :: DF [Expr]
makeBetaAxioms = do
  red <- dfRedex <$> get
  concat <$> mapM makeBetaEq red


makeBetaEq :: Expr -> DF [Expr]
makeBetaEq e = mapM defuncExpr $ makeEqForAll (normalizeLams e) (normalize e)


makeEq :: Expr -> Expr -> Expr
makeEq e1 e2
  | e1 == e2  = PTrue
  | otherwise = EEq e1 e2


makeEqForAll :: Expr -> Expr -> [Expr]
makeEqForAll e1 e2 =
  [ makeEq (closeLam su e1') (closeLam su e2') | su <- instantiate xs] -- , su2 <- instantiate xs]
  where
    (xs1, e1') = splitPAll [] e1
    (xs2, e2') = splitPAll [] e2
    xs         = L.nub (xs1 ++ xs2)

    closeLam ((x, (y,s)):su) e = ELam (y,s) (subst1 (closeLam su e) (x, EVar y))
    closeLam []              e = e

    splitPAll acc (PAll xs e) = splitPAll (acc ++ xs) e
    splitPAll acc e           = (acc, e)

instantiate :: [(Symbol, Sort)] -> [[(Symbol, (Symbol,Sort))]]
instantiate [] = [[]]
instantiate xs = go [] xs
  where
    go acc [] = acc
    go acc (x:xs) = go (combine (instOne x) acc) xs

    instOne (x, s) = [(x, (makeLamArg s i, s)) | i <- [1..maxLamArg]]

    combine xs []  = [[x] | x <- xs]
    combine xs acc =  concat [(x:) <$> acc | x <- xs]

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

txStr :: Bool -> Expr -> DF Expr
txStr flag e = if flag then return $ mapExpr goStr e else mapMExpr goNoStr e
  where
    goStr e@(EApp _ _)
      | Just a <- isStringLen e
      = makeStringLen a
    goStr e
       = e
    goNoStr (ESym s)
      = logSym s >> (return $ symbolExpr s)
    goNoStr e
      = return e


isStringLen :: Expr -> Maybe Expr
isStringLen e
  = case eliminate e of
     EApp (EVar f) a | Thy.genLen == f && hasStringArg e
                     -> Just a
     _               -> Nothing
  where
    hasStringArg (ECst e _) = hasStringArg e
    hasStringArg (EApp _ a) = isString $ exprSort a
    hasStringArg _          = False

-------------------------------------------------------------------------------
--------  Extensionality  -----------------------------------------------------
-------------------------------------------------------------------------------

txExtensionality :: Expr -> Expr
txExtensionality = mapExpr' go
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
  defunc fi = do cm'    <- defunc $ cm    fi
                 ws'    <- defunc $ ws    fi
                 setBinds $ mconcat ((senv <$> (M.elems $ cm fi)) ++ (wenv <$> (M.elems $ ws fi)))
                 gLits' <- defunc $ gLits fi
                 dLits' <- defunc $ dLits fi
                 bs'    <- defunc $ bs    fi
                 quals' <- defunc $ quals fi
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
  defunc sc = do crhs' <- defunc $ _crhs sc
                 return $ sc {_crhs = crhs'}

instance Defunc (WfC a)   where
  defunc wf = do wrft' <- defunc $ wrft wf
                 return $ wf {wrft = wrft'}

instance Defunc Qualifier where
  defunc q = do qParams' <- defunc $ qParams q
                withExtendedEnv (qParams q) $ withNoEquivalence $ do
                qBody'   <- defunc $ qBody   q
                return    $ q {qParams = qParams', qBody = qBody'}

instance Defunc SortedReft where
  defunc (RR s r) = RR <$> defunc s <*> defunc r

instance Defunc (Symbol, SortedReft) where
  defunc (x, (RR s (Reft (v, e))))
    = (x,) <$> defunc (RR s (Reft (x, subst1 e (v, EVar x))))

instance Defunc Reft where
  defunc (Reft (x, e)) = Reft . (x,) <$> defunc e

instance Defunc (a, Sort, c) where
  defunc (x, y, z) = (x, , z) <$> defunc y

instance Defunc (a, Sort) where
  defunc (x, y) = (x, ) <$> defunc y

instance Defunc a => Defunc (SEnv a) where
  defunc = mapMSEnv defunc

instance Defunc BindEnv   where
  defunc bs = do dfbs <- dfbenv <$> get
                 let f (i, xs) = if i `memberIBindEnv` dfbs
                                       then  (i,) <$> defunc xs
                                       else  (i,) <$> matchSort xs
                 mapWithKeyMBindEnv f bs
   where
    -- The refinement cannot be elaborated thus defunc-ed because
    -- the bind does not appear in any contraint,
    -- thus unique binders does not perform properly
    -- The sort should be defunc, to ensure same sort on double binders
    matchSort (x, RR s r) = ((x,) . (`RR` r)) <$> defunc s

instance Defunc a => Defunc [a] where
  defunc = mapM defunc

instance (Defunc a, Eq k, Hashable k) => Defunc (M.HashMap k a) where
  defunc m = M.fromList <$> mapM (secondM defunc) (M.toList m)

type DF    = State DFST

type DFEnv = SEnv Sort

data DFST
  = DFST { fresh   :: !Int
         , dfenv   :: !DFEnv
         , dfbenv  :: !IBindEnv
         , df_lam  :: !Bool   -- normalize lams
         , f_ext   :: !Bool   -- enable extensionality axioms
         , a_eq    :: !Bool   -- enable alpha equivalence axioms
         , b_eq    :: !Bool   -- enable beta equivalence axioms
         , f_norm  :: !Bool   -- enable normal form axioms
         , dfHO    :: !Bool   -- allow higher order thus defunctionalize
         , lamNorm :: !Bool
         , dfStr   :: !Bool   -- string interpretation
         , dfLams  :: ![Expr] -- lambda expressions appearing in the expressions
         , dfRedex :: ![Expr] -- redexes appearing in the expressions
         , dfLog   :: !String
         , dfSyms  :: ![SymConst] -- symbols in the refinements
         }

makeInitDFState :: Config -> SInfo a -> DFST
makeInitDFState cfg si
  = DFST { fresh   = 0
         , dfenv   = fromListSEnv xs
         , dfbenv  = mempty
         , df_lam  = True
         , f_ext   = extensionality   cfg
         , a_eq    = alphaEquivalence cfg
         , b_eq    = betaEquivalence  cfg
         , f_norm  = normalForm       cfg
         , dfHO    = (allowHO         cfg  || defunction cfg)
         , lamNorm = True
         -- INVARIANT: lambads and redexes are not defunctionalized
         , dfLams  = []
         , dfRedex = []
         , dfSyms  = []
         , dfLog   = ""
         , dfStr   = stringTheory cfg
         }
  where
    xs = symbolSorts cfg si ++ concat [ [(x,s), (y,s)] | (_, x, RR s (Reft (y, _))) <- bindEnvToList $ bs si]


setBinds :: IBindEnv -> DF ()
setBinds e = modify $ \s -> s{dfbenv = e}


writeLog :: String -> DF ()
writeLog str = modify $ \s -> s{dfLog =  (dfLog s) ++ "\n" ++ str}

withExtendedEnv ::  [(Symbol, Sort)] -> DF a -> DF a
withExtendedEnv bs act = do
  env <- dfenv <$> get
  let env' = foldl (\env (x, t) -> insertSEnv x t env) env bs
  modify $ \s -> s{dfenv = env'}
  r <- act
  modify $ \s -> s{dfenv = env}
  return r

withNoLambdaNormalization :: DF a -> DF a
withNoLambdaNormalization act = do
  lamNorm <- df_lam <$> get
  modify $ \s -> s{df_lam = False}
  r <- act
  modify $ \s -> s{df_lam = lamNorm}
  return r



withNoEquivalence :: DF a -> DF a
withNoEquivalence act = do
  aEq <- a_eq <$> get
  bEq <- b_eq <$> get
  modify $ \s -> s{a_eq = False, b_eq = False}
  r <- act
  modify $ \s -> s{a_eq = aEq,   b_eq = bEq}
  return r

freshSym :: DF Symbol
freshSym = do
  n  <- fresh <$> get
  modify $ \s -> s{fresh = n + 1}
  return $ intSymbol "lambda_fun_" n


mapExpr' :: (Expr -> Expr) -> Expr -> Expr
mapExpr' f e = go e
  where
    go (ELam bs e)     = f (ELam bs (go e))
    go (ECst e s)      = f (ECst (go e) s)
    go (EApp e1 e2)    = f (EApp (go e1) (go e2))
    go e@(ESym _)      = f e
    go e@(ECon _)      = f e
    go e@(EVar _)      = f e
    go (ENeg e)        = f $ ENeg (go e)
    go (EBin b e1 e2)  = f $ EBin b (go e1) (go e2)
    go (EIte e e1 e2)  = f $ EIte (go e) (go e1) (go e2)
    go (ETAbs e t)     = f $ ETAbs (go e) t
    go (ETApp e t)     = f $ ETApp (go e) t
    go (PAnd es)       = f $ PAnd $ map go es
    go (POr es)        = f $ POr  $ map go es
    go (PNot e)        = f $ PNot $ go e
    go (PImp e1 e2)    = f $ PImp (go e1) (go e2)
    go (PIff e1 e2)    = f $ PIff (go e1) (go e2)
    go (PAtom a e1 e2) = f $ PAtom a (go e1) (go e2)
    go (PAll bs e)     = f $ PAll bs   $  go e
    go (PExist bs e)   = f $ PExist bs $ go e
    go e@(PKVar _ _ )  = f e
    go e@PGrad         = f e
