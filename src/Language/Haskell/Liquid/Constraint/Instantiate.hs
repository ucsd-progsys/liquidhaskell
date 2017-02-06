{-# LANGUAGE ImplicitParams        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE FlexibleInstances     #-}

--------------------------------------------------------------------------------
-- | Axiom Instantiation  ------------------------------------------------------
--------------------------------------------------------------------------------

module Language.Haskell.Liquid.Constraint.Instantiate (

  instantiateAxioms

  ) where


import           Language.Fixpoint.Misc           (mapFst)
import           Language.Fixpoint.Types hiding (Eq)
import qualified Language.Fixpoint.Types as F        
import           Language.Fixpoint.Types.Visitor (eapps, kvars)            

import           Language.Haskell.Liquid.Constraint.Types hiding (senv)
import           Language.Haskell.Liquid.Constraint.Init  (getEqBody)
import           Language.Haskell.Liquid.GHC.Misc (dropModuleNames)
-- import           Language.Fixpoint.Types.Config (Config)

import Language.Fixpoint.Smt.Interface (checkValid', Context, smtPop, smtPush, smtDecls, smtAssert)
import Language.Fixpoint.Defunctionalize (defuncAny, Defunc, makeLamArg)
import Language.Fixpoint.SortCheck (elaborate, Elaborate)
import qualified Language.Fixpoint.Smt.Theories as FT
import Control.Monad.State 

import qualified Data.HashMap.Strict                           as M
import qualified Data.List as L 
-- import Data.Maybe (catMaybes)

import Data.Maybe 
import Data.Char (isUpper)

import System.IO.Unsafe

import qualified Debug.Trace as T 

trace :: AxiomEnv -> String -> a -> a 
trace aenv str x 
  | aenvVerbose aenv
  = T.trace str x 
  | otherwise
  = x 

instantiateAxioms :: BindEnv -> SEnv Sort -> AxiomEnv -> FixSubC -> FixSubC
instantiateAxioms _ _ aenv sub
  | not (aenvExpand aenv sub)
  = sub  
instantiateAxioms bds fenv aenv sub 
  = strengthenLhs (pAnd $ trace aenv msg (is0 ++ is ++ evalEqs)) sub
  where
    is0 = eqBody <$> L.filter (null . eqArgs) (aenvEqs  aenv)
    msg = "\n\nLiquid Instantiation with " ++ show (L.intercalate "and" methods) ++ "\n\n"
    methods = catMaybes [if aenvDoEqs aenv sub then Just "arithmetic" else Nothing , 
                         if aenvDoRW  aenv sub then Just "rewrite"    else Nothing
                        ] :: [String]
    is               = if aenvDoEqs aenv sub then instances maxNumber aenv (trace aenv initMsg $ initOccurences) else []
    evalEqs          = if aenvDoRW  aenv sub 
                         then trace aenv evalMsg [ PAtom F.Eq  e e'|(e, e') <- evaluate ((vv Nothing, slhs sub):binds) fenv as aenv initExpressions, e /= e'] 
                         else [] 
    initExpressions  = (expr $ slhs sub):(expr $ srhs sub):(expr <$> binds)
    binds            = envCs bds (senv sub)
    initOccurences   = concatMap (makeInitOccurences as eqs) initExpressions

    as  = (,fuelNumber) . eqName <$> (filter (not . null . eqArgs) $ aenvEqs aenv)
    eqs = aenvEqs  aenv

    showMaybeVar sub   = case subVar sub of 
                           Just x  -> " for " ++ show x
                           Nothing -> "" 

    fuelNumber    = aenvFuel aenv sub 
    initOccNumber = length initOccurences
    axiomNumber   = length $ aenvSyms aenv
    maxNumber     = (axiomNumber * initOccNumber) ^ fuelNumber
    initMsg = "\nStart instantiation" ++ showMaybeVar sub ++ 
              " with fuel = " ++ show fuelNumber ++ " init occurences = " ++ show initOccNumber ++ " axioms = " ++ show axiomNumber ++ 
              " can generate up to " ++ show maxNumber ++ " instantiations\n" ++ 
              "\n\nShow simplifies "  ++ show (aenvSimpl aenv) ++ evalMsg
    evalMsg = "\n\nStart Rewriting" 


makeKnowledge :: AxiomEnv -> SEnv Sort -> [(Symbol, SortedReft)] -> ([(Expr, Expr)], Knowledge) 
makeKnowledge aenv fenv es = trace aenv ("\n\nMY KNOWLEDGE= \n\n" ++ -- showpp (expr <$> es) ++ 
                              -- "INIT KNOWLEDGE\n" ++  
                              -- L.intercalate "\n" (showpp <$> es) ++ 
                              -- L.intercalate "\n" (showpp <$> filter noPKVar (expr <$> es)) ++ 
                              -- if null tes then "" else "\n\nTRUES = \n\n" ++ showpp tes ++ 
                              -- if null fes then "" else "\n\nFALSE\n\n" ++ showpp fes ++ 
                              -- if null sels then "" else "\n\nSELECTORS\n\n" ++ showpp sels ++ 
                              -- if null eqs then "" else "\n\nAxioms\n\n" ++ showpp eqs ++
                              -- "\n\nEnvironment \n\n" ++ showpp es ++
                              -- if null proofs then "" else "\n\nProofs\n\n" ++ showpp proofs ++
                              -- if null eqs' then "" else "\n\nCheckers\n\n" ++ showpp eqs' ++
                              "\n" )  
                             (simpleEqs,) $ (emptyKnowledge context) 
                                 { knSels   = sels
                                 , knEqs    = eqs
                                 , knSims   = aenvSimpl aenv
                                 , knAms = aenvEqs aenv
                                 , knPreds = askSMT 
                                 }
  where
    (xv, sv) = (vv Nothing,  sr_sort $ snd $ head es)
    context :: Context
    context = unsafePerformIO $ do 
      smtPop (aenvContext aenv)
      smtPush (aenvContext aenv)
      smtDecls (aenvContext aenv) $ L.nub [(x, toSMT xv sv [] aenv senv s) | (x, s) <- fbinds, not (M.member x FT.theorySymbols)] 
      -- smtDecl (aenvContext aenv) xv sv 
      smtAssert (aenvContext aenv) (pAnd ([toSMT xv sv [] aenv senv $ PAtom F.Eq e1 e2 |  (e1, e2) <- simpleEqs] ++ filter noPKVar ((toSMT xv sv [] aenv senv . expr) <$> es)))
      return (aenvContext aenv)

    fbinds = toListSEnv fenv ++ [(x, s) | (x, RR s _) <- es]

    senv = fromListSEnv fbinds

    noPKVar = null . kvars

    askSMT :: Context -> [(Symbol, Sort)] -> Expr -> Bool 
    askSMT _ _ e     | isTautoPred e = True 
    askSMT _ _ e     | isFalse e     = False 
    askSMT cxt xss e | noPKVar e = unsafePerformIO $ do
        smtPush cxt
        b <- checkValid' cxt [] 
                             PTrue -- (pAnd ([toSMT xv sv [] aenv $ PAtom F.Eq e1 e2 |  (e1, e2) <- simpleEqs] ++ filter noPKVar ((toSMT xv sv [] aenv . expr) <$> es))) 
                             (toSMT xv sv xss aenv senv e) 
        smtPop cxt
        return b   
    askSMT _ _ _ = False

    proofs = filter isProof es
    eqs = [(EVar x, ex) | Eq a _ bd <- filter ((null . eqArgs)) $ aenvEqs aenv, PAtom F.Eq (EVar x) ex <- splitPAnd bd, x == a, EVar x /= ex ] 
    -- This creates the rewrite rule e1 -> e2 
    -- when should I apply it?
    -- 1. when e2 is a data con and can lead to further reductions 
    -- 2. when size e2 < size e1 
    simpleEqs = concatMap (makeSimplifications (aenvSimpl aenv)) dcEqs 
    dcEqs = L.nub $ catMaybes $ [getDCEquality e1 e2 | PAtom F.Eq e1 e2 <- concatMap splitPAnd (expr <$> proofs)]
    sels  = concatMap go $ map expr es
    go e = let es  = splitPAnd e
               su  = mkSubst [(x, EVar y) | PAtom F.Eq (EVar x) (EVar y) <- es ]
               sels = [(EApp (EVar s) x, e) | PAtom F.Eq (EApp (EVar s) x) e <- es, isSelector s ]
           in L.nub (sels ++ subst su sels)

    isSelector :: Symbol -> Bool 
    isSelector  = L.isPrefixOf "select" . symbolString 

    isProof (_, RR s _) =  showpp s == "Tuple"


toSMT :: (Elaborate a, Defunc a) => Symbol -> Sort -> [(Symbol, Sort)] -> AxiomEnv -> SEnv Sort -> a -> a 
toSMT xv sv xs aenv senv  
  = defuncAny (aenvConfig aenv) (insertSEnv xv sv senv) . 
    elaborate "symbolic evaluation" (foldl (\env (x,s) -> insertSEnv x s (deleteSEnv x env)) (insertSEnv xv sv senv) xs) 


makeSimplifications :: [Simplify] -> (Symbol, [Expr], Expr) -> [(Expr, Expr)]
makeSimplifications sis (dc, es, e)
 = catMaybes $ map go sis 
 where
   go (SMeasure f dc' xs bd) 
     | dc == dc', length xs == length es 
     = Just (EApp (EVar f) e, subst (mkSubst $ zip xs es) bd)
   go _ 
     = Nothing 


getDCEquality :: Expr -> Expr -> Maybe (Symbol, [Expr], Expr)
getDCEquality e1 e2 
    | Just dc1 <- f1
    , Just dc2 <- f2
    = if dc1 == dc2 then Nothing else error ("isDCEquality on" ++ showpp e1 ++ "\n" ++ showpp e2) 
    | Just dc1 <- f1
    = Just (dc1, es1, e2) 
    | Just dc2 <- f2
    = Just (dc2, es2, e1)
    | otherwise  
    = Nothing 
  where
    (f1, es1) = mapFst getDC $ splitEApp e1 
    (f2, es2) = mapFst getDC $ splitEApp e2 

    getDC (EVar x) 
        = if isUpper $ head $ symbolString $  dropModuleNames x then Just x else Nothing  
    getDC _ 
        = Nothing

splitPAnd :: Expr -> [Expr]
splitPAnd (PAnd es) = concatMap splitPAnd es 
splitPAnd e         = [e]

evaluate :: [(Symbol, SortedReft)] -> SEnv Sort -> FuelMap -> AxiomEnv -> [Expr] -> [(Expr, Expr)] 
evaluate facts fenv fm' aenv einit 
  = eqs ++ (concat $ catMaybes [evalOne e | e <- L.nub $ concatMap grepTopApps einit]) 
  where
    fm = [(x, 10 * i) | (x, i)<- fm']
    (eqs, γ) = makeKnowledge aenv fenv facts
    initEvalSt = EvalEnv 0 fm [] aenv
    evalOne :: Expr -> Maybe [(Expr, Expr)]
    evalOne e = let (e', _) = runState (eval γ e) initEvalSt
                in case e' == e of 
                    True -> Nothing
                    False -> trace aenv ("\n\nEVALUATION OF \n\n" ++ showpp e ++ "\nIS\n" ++ showpp e') 
                                Just [(e,e')] 
                                   -- This adds all intermediate unfoldings into the assumptions
                                   -- no test needs it
                                   -- TODO: add a flag to enable it
                                   -- ((e, e'):evSequence st)


data EvalEnv = EvalEnv { evId        :: Int
                       , _evFuelMap   :: FuelMap
                       , evSequence  :: [(Expr,Expr)]
                       , evAEnv      :: AxiomEnv
                       }

returnTrace :: String -> Expr -> Expr -> EvalST Expr 
returnTrace str e e'
  = do env <- get 
       return $ 
           trace (evAEnv env) 
             ("\nEval " ++ show (evId env) ++ " by " ++ str ++ " :\n" ++ 
             showpp e ++ " ~> " ++ showpp e' ++ "\n")
             e'

addApplicationEq :: Knowledge -> Expr -> Expr -> EvalST ()
addApplicationEq γ e1 e2 = 
  modify $ (\st -> st{evSequence = (makeLam e1, makeLam e2):evSequence st})
  where
    makeLam e = foldl (\e xs -> ELam xs e) e (knLams γ)


(~>) :: (Expr, String) -> Expr -> EvalST Expr
(e,str) ~> e' = do 
    modify $ (\st -> st{evId = evId st + 1})
    returnTrace str e (normalizeEval e')


eval :: Knowledge -> Expr -> EvalST Expr 

eval γ e | Just e' <- lookupKnowledge γ e
   = (e, "Knowledge") ~> e' 

eval γ (ELam (x,s) e)
  = do let x' = makeLamArg s (1+(length $ knLams γ))  
       e'    <- eval γ{knLams = (x',s):knLams γ} (subst1 e (x, EVar x'))
       return $ ELam (x,s) $ subst1 e' (x', EVar x)

eval γ (PAtom r e1 e2)
  = PAtom r <$> eval γ e1 <*> eval γ e2 

eval γ e@(EIte b e1 e2)
  = do b' <- eval γ b 
       evalIte γ e b' e1 e2 

eval γ e@(EApp _ _)
  = evalArgs γ e >>= evalApp γ e 

eval _ e 
  = do _env <- evAEnv <$> get 
       return $ e -- trace env ("\n\nEvaluation stops at " ++ showpp e) e


evalArgs :: Knowledge -> Expr -> EvalST (Expr, [Expr])
evalArgs γ e = go [] e
  where
    go acc (EApp f e)
      = do f' <- eval γ f 
           e' <- eval γ e 
           go (e':acc) f' 
    go acc e 
      = do e' <- eval γ e 
           return (e', acc)

evalApp :: Knowledge -> Expr -> (Expr, [Expr]) -> EvalST Expr
evalApp γ e (EVar f, [ex])
  | (EVar dc, es) <- splitEApp ex
  , Just simp <- L.find (\simp -> (smName simp == f) && (smDC simp == dc)) (knSims γ)
  , length (smArgs simp) == length es 
  = do e'    <- eval γ $ normalizeEval $ substPopIf (zip (smArgs simp) es) (smBody simp) 
       (e, "Simplify-" ++ showpp f) ~> e'

evalApp γ _ (EVar f, es)
  | Just eq <- L.find ((==f) . eqName) (knAms γ)
  , Just bd <- getEqBody eq 
  , length (eqArgs eq) == length es
  , not (f `elem` syms bd) -- not recursive 
  = eval γ $ normalizeEval $ substPopIf (zip (eqArgs eq) es) bd


evalApp γ _e (EVar f, es)
  | Just eq <- L.find ((==f) . eqName) (knAms γ)
  , Just bd <- getEqBody eq 
  , length (eqArgs eq) == length es  --  recursive 
  = evalRecApplication γ (eApps (EVar f) es) $ subst (mkSubst $ zip (eqArgs eq) es) bd

evalApp _ _ (f, es)
  = return $ eApps f es


evalRecApplication :: Knowledge ->  Expr -> Expr -> EvalST Expr 
evalRecApplication γ e (EIte b e1 e2)
  = do b' <- eval γ b 
       if isValid γ b'
          then addApplicationEq γ e e1 >> eval γ e1 >>= ((e, "App") ~>)
          else if isValid γ (PNot b')
          then addApplicationEq γ e e2 >> eval γ e2 >>= ((e, "App") ~>)
          else return e --  T.trace ("FAIL TO EVALUATE\n" ++ showpp b' ++ "\nOR\n" ++ showpp b )  e 
evalRecApplication _ _ e 
  = return e 

isValid :: Knowledge -> Expr -> Bool 
isValid γ b = knPreds γ (knContext γ) (knLams γ) b


evalIte :: Knowledge -> Expr -> Expr -> Expr -> Expr -> EvalST Expr
evalIte γ e b e1 _ 
  | isValid γ b  
  = do e' <- eval γ e1
       (e, ("If-True of:" ++ showpp b))  ~> e'
evalIte γ e b _ e2 
  | isValid γ (PNot b)
  = do e' <- eval γ e2
       (e, "If-False") ~> e'
evalIte γ _ b e1 e2 
  = do e1' <- eval γ e1 
       e2' <- eval γ e2 
       return $ EIte b e1' e2' 


substPopIf :: [(Symbol, Expr)] -> Expr -> Expr 
substPopIf xes e = normalizeEval $ foldl go e xes  
  where
    go e (x, EIte b e1 e2) = EIte b (subst1 e (x, e1)) (subst1 e (x, e2)) 
    go e (x, ex)           = subst1 e (x, ex) 

-- normalization required by ApplicativeMaybe.composition

normalizeEval :: Expr -> Expr  
normalizeEval = snd . go 
  where
    go (EIte b t f) | isTautoPred t && isFalse f = (True, b) 
    go (EIte b e1 e2) = let (fb, b') = go b
                            (f1, e1') = go e1 
                            (f2, e2') = go e2 
                        in  (fb || f1 || f2, EIte b' e1' e2')
    go (EApp (EIte b f1 f2) e) = (True, EIte b (snd $ go $ EApp f1 e) (snd $ go $ EApp f2 e))
    go (EApp f (EIte b e1 e2)) = (True, EIte b (snd $ go $ EApp f e1) (snd $ go $ EApp f e2))
    go (EApp e1 e2)            = let (f1, e1') = go e1 
                                     (f2, e2') = go e2 
                                 in if f1 || f2 then go $ EApp e1' e2' else (False, EApp e1' e2')
    go e = (False, e)


data Knowledge 
  = KN { knSels   :: ![(Expr, Expr)]
       , knEqs    :: ![(Expr, Expr)]
       , knSims   :: ![Simplify]
       , knAms    :: ![Equation]
       , knContext :: !Context
       , knPreds  :: !(Context -> [(Symbol, Sort)] -> Expr -> Bool)
       , knLams   :: [(Symbol, Sort)]
       }

emptyKnowledge :: Context -> Knowledge
emptyKnowledge cxt = KN [] [] [] [] cxt (\_ _ _ -> False) []

lookupKnowledge :: Knowledge -> Expr -> Maybe Expr 
lookupKnowledge γ e 
  -- Zero argument axioms like `mempty = N`
  | Just e' <- L.lookup e (knEqs γ)  
  = Just e'
  | Just e' <- L.lookup e (knSels γ) 
  = Just e'
  | otherwise 
  = Nothing 

type EvalST = State EvalEnv

grepTopApps :: Expr -> [Expr] 
grepTopApps (PAnd es) = concatMap grepTopApps es 
grepTopApps (PAtom _ e1 e2) = (grepTopApps e1) ++ (grepTopApps e2)
grepTopApps e@(EApp _ _) = [e]
grepTopApps _ = [] 


instances :: Int -> AxiomEnv -> [Occurence] -> [Expr] 
instances maxIs aenv !occs 
  = instancesLoop aenv maxIs eqs occs -- (eqBody <$> eqsZero) ++ is
  where
    eqs = filter (not . null . eqArgs) (aenvEqs  aenv)

-- Currently: Instantiation happens arbitrary times (in recursive functions it diverges)
-- Step 1: Hack it so that instantiation of axiom A happens from an occurences and its 
-- subsequent instances <= FUEL times 
-- How? Hack expressions to contatin fuel info within eg Cst
-- Step 2: Compute fuel based on Ranjit's algorithm

instancesLoop :: AxiomEnv ->  Int -> [Equation] -> [Occurence] -> [Expr]
instancesLoop aenv maxIns eqs = go 0 [] 
  where 
    go :: Int -> [Expr] -> [Occurence] -> [Expr]
    go !i acc occs = let is      = concatMap (unfold eqs) occs 
                         newIs   = findNewEqs is acc 
                         newOccs = concatMap (grepOccurences eqs) newIs
                         msg     = show (i + length newIs) ++ "/" ++ (show maxIns) ++ "\t\t"
                     in  if null newIs then acc else go (trace aenv msg (i + length newIs)) ((fst <$> newIs) ++ acc) newOccs

{- 
maxFuelMap :: [Occurence] -> FuelMap
maxFuelMap occs = mergeMax <$> L.transpose (ofuel <$> occs)
  where 
    mergeMax :: FuelMap -> (Symbol, Fuel)
    mergeMax xfs = let (xs, fs) = unzip xfs in (head xs, maximum fs)
-}

findNewEqs :: [(Expr, FuelMap)] -> [Expr] -> [(Expr, FuelMap)]
findNewEqs [] _ = []
findNewEqs ((e, f):xss) es 
  | e `elem` es = findNewEqs xss es 
  | otherwise   = (e,f):findNewEqs xss es 

makeInitOccurences :: [(Symbol, Fuel)] -> [Equation] -> Expr -> [Occurence]
makeInitOccurences xs eqs e 
  = [Occ x es xs | (EVar x, es) <- splitEApp <$> eapps e
                 , Eq x' xs' _ <- eqs, x == x'
                 , length xs' == length es]  

grepOccurences :: [Equation] -> (Expr, FuelMap) -> [Occurence]
grepOccurences eqs (e, fs) 
  = filter (goodFuelMap . ofuel)  
           [Occ x es fs | (EVar x, es) <- splitEApp <$> eapps e
                        , Eq x' xs' _ <- eqs, x == x'
                        , length xs' == length es]  

goodFuelMap :: FuelMap -> Bool 
goodFuelMap = any ((>0) . snd)

unfold :: [Equation] -> Occurence -> [(Expr, FuelMap)]
unfold eqs (Occ x es fs) 
  = catMaybes [if hasFuel fs x then Just (subst (mkSubst $ zip  xs' es) e, makeFuelMap (\x -> x-1) fs x) else Nothing 
              | Eq x' xs' e <- eqs
              , x == x'
              , length xs' == length es]  

hasFuel :: FuelMap -> Symbol -> Bool 
hasFuel fm x = maybe True (\x -> 0 < x) (L.lookup x fm)


makeFuelMap :: (Fuel -> Fuel) -> FuelMap -> Symbol -> FuelMap

makeFuelMap f ((x, fx):fs) y  
  | x == y    = (x, f fx) : fs
  | otherwise = (x, fx)   : makeFuelMap f fs y
makeFuelMap _ _ _ = error "makeFuelMap"

data Occurence = Occ {_ofun :: Symbol, _oargs :: [Expr], ofuel :: FuelMap}
 deriving (Show)

type Fuel = Int 

type FuelMap = [(Symbol, Fuel)]



{- 
showExpr :: Expr -> String 
showExpr (PAnd eqs) 
  = L.intercalate "\n" (showpp . lhs <$> eqs )
  where
    lhs (PAtom F.Eq l _) = l 
    lhs e                = e 
showExpr e = showpp e 
-}


instance Expression (Symbol, SortedReft) where
  expr (x, RR _ (Reft (v, r))) = subst1 (expr r) (v, EVar x)
