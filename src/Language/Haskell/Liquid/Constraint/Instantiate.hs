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


import           Language.Fixpoint.Misc           (mapSnd, mapFst)
import           Language.Fixpoint.Types hiding (Eq)
import qualified Language.Fixpoint.Types as F        
import           Language.Fixpoint.Types.Visitor (eapps)            

import           Language.Haskell.Liquid.Constraint.Types hiding (senv)
import           Language.Haskell.Liquid.Constraint.Init  (getEqBody)
import           Language.Haskell.Liquid.GHC.Misc (dropModuleNames)

import Control.Monad.State 

import qualified Data.List as L 
-- import Data.Maybe (catMaybes)

import Data.Maybe 
import Data.Char (isUpper)

import qualified Debug.Trace as T 

trace :: AxiomEnv -> String -> a -> a 
trace aenv str x 
  | aenvVerbose aenv
  = T.trace str x 
  | otherwise
  = x 

instantiateAxioms :: BindEnv  -> AxiomEnv -> FixSubC -> FixSubC
instantiateAxioms _  aenv sub
  | not (aenvExpand aenv sub)
  = sub  
instantiateAxioms bds aenv sub 
  = strengthenLhs (pAnd $ trace aenv msg (is0 ++ is ++ evalEqs)) sub
  where
    is0 = eqBody <$> L.filter (null . eqArgs) (aenvEqs  aenv)
    msg = "\n\nLiquid Instantiation with " ++ show (L.intercalate "and" methods) ++ "\n\n"
    methods = catMaybes [if aenvDoEqs aenv sub then Just "arithmetic" else Nothing , 
                         if aenvDoRW  aenv sub then Just "rewrite"    else Nothing
                        ] :: [String]
    is               = if aenvDoEqs aenv sub then instances maxNumber aenv (trace aenv initMsg $ initOccurences) else []
    evalEqs          = if aenvDoRW  aenv sub 
                         then trace aenv evalMsg [ PAtom F.Eq  e e'|(e, e') <- evaluate ((dummySymbol, slhs sub):binds) as aenv initExpressions, e /= e'] 
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


makeKnowledge :: AxiomEnv -> [(Symbol, SortedReft)] -> ([(Expr, Expr)], Knowledge) 
makeKnowledge aenv es = trace aenv ("\n\nMY KNOWLEDGE= \n\n" ++ -- showpp (expr <$> es) ++  
                              -- if null tes then "" else "\n\nTRUES = \n\n" ++ showpp tes ++ 
                              -- if null fes then "" else "\n\nFALSE\n\n" ++ showpp fes ++ 
                              -- if null sels then "" else "\n\nSELECTORS\n\n" ++ showpp sels ++ 
                              -- if null eqs then "" else "\n\nAxioms\n\n" ++ showpp eqs ++
                              -- "\n\nEnvironment \n\n" ++ showpp es ++
                              -- if null proofs then "" else "\n\nProofs\n\n" ++ showpp proofs ++
                              -- if null eqs' then "" else "\n\nCheckers\n\n" ++ showpp eqs' ++
                              "\n" )  
                             (simpleEqs,) $ emptyKnowledge {knTrues = tes, knFalses = fes, knSels =  sels, knEqs = eqs, knSims = aenvSimpl aenv, knChecks = eqs', knAms = aenvEqs aenv}
  where
    proofs = filter isProof es
    eqs = [(EVar x, ex) | Eq a _ bd <- filter ((null . eqArgs)) $ aenvEqs aenv, PAtom F.Eq (EVar x) ex <- splitPAnd bd, x == a, EVar x /= ex ] 
    -- This creates the rewrite rule e1 -> e2 
    -- when should I apply it?
    -- 1. when e2 is a data con and can lead to further reductions 
    -- 2. when size e2 < size e1 
    simpleEqs = concatMap (makeSimplifications (aenvSimpl aenv)) dcEqs 
    eqs'      = [(e, dc) | (dc, _, e) <- dcEqs]
    dcEqs = L.nub $ catMaybes $ [getDCEquality e1 e2 | PAtom F.Eq e1 e2 <- concatMap splitPAnd (expr <$> proofs)
                                 , not (dummySymbol `elem` (syms e1 ++ syms e2))]
    (tes, fes, sels) = mapThd3 concat $ mapSnd3 concat $ mapFst3 concat $ unzip3 (map go $ map expr es)
    go e = let es  = splitPAnd e
               su  = mkSubst [(x, EVar y) | PAtom F.Eq (EVar x) (EVar y) <- es ]
               tes = [e | PIff e t <- es, isTautoPred t] 
               fes = [e | PIff e f <- es, isFalse f ]  
               sels = [(EApp (EVar s) x, e) | PAtom F.Eq (EApp (EVar s) x) e <- es, isSelector s ]
           in (L.nub (tes ++ subst su tes), L.nub (fes ++ subst su fes), L.nub (sels ++ subst su sels))

    isSelector :: Symbol -> Bool 
    isSelector  = L.isPrefixOf "select" . symbolString 
    mapFst3 f (x, y, z) = (f x, y, z)
    mapSnd3 f (x, y, z) = (x, f y, z)
    mapThd3 f (x, y, z) = (x, y, f z)

    isProof (_, RR s _) =  showpp s == "Tuple"


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


evaluate :: [(Symbol, SortedReft)] -> FuelMap -> AxiomEnv -> [Expr] -> [(Expr, Expr)] 
evaluate facts fm' aenv einit 
  = eqs ++ catMaybes [evalOne e | e <- L.nub $ concatMap grepTopApps einit] 
  where
    fm = [(x, 10 * i) | (x, i)<- fm']
    (eqs, γ) = makeKnowledge aenv facts
    initEvalSt = EvalEnv 0 fm [] aenv
    evalOne e = let e' = evalState (eval γ e) initEvalSt
                in case e' == e of 
                    True -> Nothing
                    False -> trace aenv ("\n\nEVALUATION OF \n\n" ++ showpp e ++ "\nIS\n" ++ showpp e') 
                                Just (e, e')


data EvalEnv = EvalEnv { evId        :: Int
                       , _evFuelMap   :: FuelMap
                       , evSequence  :: [Expr]
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

(~>) :: (Expr, String) -> Expr -> EvalST Expr
(e,str) ~> e' = do 
    modify $ (\st -> st{evId = evId st + 1, evSequence = e:evSequence st})
    returnTrace str e (normalizeEval e')


eval :: Knowledge -> Expr -> EvalST Expr 

eval γ e | Just e' <- lookupKnowledge γ e
   = (e, "Knowledge") ~> e' 

eval γ (ELam xs e)
  = ELam xs <$> eval γ e 

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
  = do e'    <- eval γ $ normalizeEval $ substPopIf (zip (smArgs simp) (id <$> es)) (smBody simp) 
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
  = evalRecApplication γ (eApps (EVar f) es) $ normalizeEval $ substPopIf (zip (eqArgs eq) es) bd

evalApp _ _ (f, es)
  = return $ eApps f es


evalRecApplication :: Knowledge ->  Expr -> Expr -> EvalST Expr 
evalRecApplication γ e (EIte b e1 e2)
  = do b' <- eval γ b 
       if isTautoPred b'
          then eval γ e1 >>= ((e, "App") ~>)
          else if isFalse b'
          then eval γ e2 >>= ((e, "App") ~>)
          else return e 
evalRecApplication _ _ e 
  = return e 




evalIte :: Knowledge -> Expr -> Expr -> Expr -> Expr -> EvalST Expr
evalIte γ e b e1 _ 
  | isTautoPred b 
  = do e' <- eval γ e1
       (e, "If-True")  ~> e'
evalIte γ e b _ e2 
  | isFalse b 
  = do e' <- eval γ e2
       (e, "If-False") ~> e'
evalIte γ _ b e1 e2 
  = do e1' <- eval γ e1 
       e2' <- eval γ e2 
       return $ EIte b e1' e2' 




{- 

    go tr fm e | Just e' <- L.lookup e sels 
      = (True, traceEval tr fm "SELECTORYEAH" e e', incrCount fm) 

    -- This eval step is required by Unification.split_fun
    -- to make the step 
    --    applyOne su (apply x (TFun t1 t2))
    -- -> applyOne su (TFun (apply x t1) (apply x t2))
    -- and then expand the applyOne 

    go tr fm e | Just e' <- L.lookup e eqs 
      = (True, traceEval tr fm "KNOWLEDGEYEAH" e e',incrCount fm) 
 
    go tr fm e@(EApp _ _) 
      = evalApp' False tr fm [] e 
    go tr fm e@(EIte b e1 e2)
      = let (_, b', fm1)  =  go tr fm b 
            (evaleated, e', fm2) = evalIte tr fm1 e b' e1 e2
            in (evaleated, e', incrCount fm2)

    go tr fm (PAtom b e1 e2)
      = let (ev1, e1', fm1) = go tr fm e1 
            (ev2, e2', fm2) = go tr fm1 e2 
        in (ev1 || ev2, PAtom b e1' e2', incrCount fm2)

    go tr fm (ELam bs e)
      = let (ev, e', fm1) = go tr fm e 
        in (ev, ELam bs e', incrCount fm1)
    go _ fm e
      = (False, e, incrCount fm) 

    evalIte tr fm e b e1 e2 
      | isTautoPred b 
      = let (_,e1', fm') = go tr fm e1
        in (True,, fm') $ normalizeIF $ traceEval tr fm "ifTrue" e e1' 
      | isFalse b 
      = let (_,e2', fm') = go tr fm e2 
        in (True,,fm') $ normalizeIF $ traceEval tr fm "IfFalse" e e2'
      |  b `elem` trueExprs
      = let (_,e1', fm') = go tr fm e1
        in (True,,fm') $ normalizeIF $ traceEval tr fm "ifTrueYEAH" e e1' 
      |  b `elem` falseExpr
      = let (_,e2', fm') = go tr fm e2 
        in (True,,fm') $ normalizeIF $ traceEval tr fm "IfFalseYEAH" e e2' 
      | otherwise 
      = (False,,fm) $ EIte b e1 e2 

    evalApp' evacc tr fm acc (EApp f e) 
      = let (fe, e', fm1)  =  go tr fm  e 
            (ff, f', fm2)  =  go tr fm1 f 
            (fm3, e'') = if fe then (fm2, e') else (fm, e)
            f'' = if ff then f' else f  
        in evalApp' (evacc || fe || ff) tr fm3 (e'':acc) f''
    evalApp' evacc tr fm acc e 
      = let (fe, e', fm') =  go tr fm e
        in if fe then evalApp True tr fm' (e', acc) else evalApp evacc tr fm (e, acc)  

    evalApp _ tr fm (EVar f, [e])
      | (EVar dc, es) <- splitEApp e
      , Just simp <- L.find (\simp -> (smName simp == f) && (smDC simp == dc)) (aenvSimpl aenv)
      , length (smArgs simp) == length es 
      = let e'  = substPopIf (zip (smArgs simp) (id <$> es)) (smBody simp) 
            e'' = normalizeIF $ traceEval tr fm "Simpl" (eApps (EVar f) [e]) e'
            (_, e''', fm') = go tr fm e''
        in (True, e''', incrCount fm') 
    evalApp ev tr (i, fm, missed) (EVar f, es)
      | Just eq <- L.find ((==f) . eqName) (aenvEqs aenv)
      , Just bd <- getEqBody eq 
      , length (eqArgs eq) == length es
      , hasFuel fm f 
      = let e'  = substPopIf (zip (eqArgs eq) (id <$> es)) bd
            e'' = normalizeIF $ traceEval tr (i, fm, []) ("App-" ++ showpp f) (eApps (EVar f) es) e'
            fm' =  makeFuelMap (\x -> x-1) fm f
            (fapp, e''', fm'') = go tr (i+1, fm', []) e''
         in if fapp then (True, e''', fm'') 
            else if (f `elem` syms bd) 
              then (ev, eApps (EVar f) es, (i, fm, (eApps (EVar f) es, e'''):missed))  
              else (True, e''', incrCount fm'')  

    evalApp ev _ fm (e, es) 
      = (ev, eApps (id e) (id <$> es), fm)


    incrCount (i, fm, tr) = (i+1, fm, tr)


    traceEval _tr (i, _, _) str !e1 !e2 
      = trace  aenv (show i ++ "\t" ++  str ++ "\t" ++ showpp einit ++  "\n" ++ showpp e1 ++ " -> " ++ showpp e2 )
      -- ("\nEVAL STEP " ++ str ++ "\n" ++ 
      --                showpp e1 ++ "\n -> \n" ++ showpp e2) 
      e2 






-}


substPopIf :: [(Symbol, Expr)] -> Expr -> Expr 
substPopIf xes e = normalizeEval $ foldl go e xes  
  where
    go e (x, EIte b e1 e2) = EIte b (subst1 e (x, e1)) (subst1 e (x, e2)) 
    go e (x, ex)           = subst1 e (x, ex) 


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
  = KN { knTrues  :: ![Expr]
       , knFalses :: ![Expr]
       , knSels   :: ![(Expr, Expr)]
       , knEqs    :: ![(Expr, Expr)]
       , knChecks :: ![(Expr, Symbol)]
       , knSims   :: ![Simplify]
       , knAms    :: ![Equation]
       }

emptyKnowledge :: Knowledge
emptyKnowledge = KN [] [] [] [] [] [] []

lookupKnowledge :: Knowledge -> Expr -> Maybe Expr 
lookupKnowledge γ e 
  -- Zero argument axioms like `mempty = N`
  | Just e' <- L.lookup e (knEqs γ)  
  = Just e'
  | e `elem` (knTrues γ)
  = Just PTrue 
  | e `elem` (knFalses γ)
  = Just PFalse 
  | Just e' <- L.lookup e (knSels γ) 
  = Just e'
  | otherwise 
  = checkChecker (knChecks γ) e 


checkChecker :: [(Expr,Symbol)] -> Expr -> Maybe Expr 
checkChecker !dcEqs !(EApp (EVar isDC) e)
  | Just dc <- L.lookup e dcEqs
  , is_ == "is_"
  = if dcName == dc then Just PTrue else Just PFalse
  where 
    (is_, dcName) = mapSnd symbol $ splitAt 3 $ symbolString isDC  

checkChecker _ _ 
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
