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


-- import           Language.Fixpoint.Misc            
import           Language.Fixpoint.Types hiding (Eq)
import qualified Language.Fixpoint.Types as F        
import           Language.Fixpoint.Types.Visitor (eapps)            

import           Language.Haskell.Liquid.Constraint.Types hiding (senv)
import           Language.Haskell.Liquid.Constraint.Init  (getEqBody)

import Control.Monad.State 

import qualified Data.List as L 
-- import Data.Maybe (catMaybes)

import Data.Maybe 

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
                         then trace aenv evalMsg [ PAtom F.Eq  e e'| es <- initExpressions, (e, e') <- evaluate ((dummySymbol, slhs sub):binds) as aenv es, e /= e'] 
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


makeKnowledge :: AxiomEnv -> [(Symbol, SortedReft)] -> Knowledge 
makeKnowledge aenv es = trace aenv ("\n\nMY KNOWLEDGE= \n\n" ++ -- showpp (expr <$> es) ++  
                              "\n\nTRUES = \n\n" ++ showpp tes ++ 
                              "\n\nFALSE\n\n" ++ showpp fes ++ 
                              "\n\nSELECTORS\n\n" ++ showpp sels ++ 
                              if null eqs then "" else "\n\nProofs\n\n" ++ showpp eqs 
                              )  
                             emptyKnowledge {knTrues = tes, knFalses = fes, knSels =  sels, knEqs = eqs, knSims = aenvSimpl aenv, knAms = aenvEqs aenv}
  where
    proofs = filter isProof es
    eqs = [(EVar x, ex) | Eq a _ bd <- filter ((null . eqArgs)) $ aenvEqs aenv, PAtom F.Eq (EVar x) ex <- splitPAnd bd, x == a, EVar x /= ex ] ++  eqs'
    -- This creates the rewrite rule e1 -> e2 
    -- when should I apply it?
    -- 1. when e2 is a data con and can lead to further reductions 
    -- 2. when size e2 < size e1 
    eqs' = L.nub $ [(e1, e2) | PAtom F.Eq e1 e2 <- concatMap splitPAnd (expr <$> proofs), not (dummySymbol `elem` (syms e1 ++ syms e2))] 
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

    isProof (_, RR s _) =  (showpp s == "Tuple")


splitPAnd :: Expr -> [Expr]
splitPAnd (PAnd es) = concatMap splitPAnd es 
splitPAnd e         = [e]


evaluate :: [(Symbol, SortedReft)] -> FuelMap -> AxiomEnv -> Expr -> [(Expr, Expr)] 
evaluate facts fm' aenv einit 
  = catMaybes [evalOne e | e <- L.nub $ grepTopApps einit] 
  where
    fm = [(x, 10 * i) | (x, i)<- fm']
    evalOne e = let γ = makeKnowledge aenv facts
                    initEvalSt = EvalEnv 0 fm [] aenv
                    e' = evalState (eval γ e) initEvalSt
                in case e' of 
                    (False, _) -> Nothing
                    (True, e') -> trace aenv ("\n\nEVALUATION OF \n\n" ++ showpp e ++ "\nIS\n" ++ showpp e') 
                                Just (e, e')


data EvalEnv = EvalEnv { evId        :: Int
                       , evFuelMap   :: FuelMap
                       , evSequence  :: [Expr]
                       , evAEnv      :: AxiomEnv
                       }

returnTrace :: String -> Expr -> Expr -> EvalST (Bool, Expr) 
returnTrace str e e'
  = do env <- get 
       return $ (True,) $ 
           trace (evAEnv env) 
             ("\nEval " ++ show (evId env) ++ " by " ++ str ++ " :\n" ++ 
             showpp e ++ " ~> " ++ showpp e' ++ "\n")
             e'

(~>) :: (Expr, String) -> Expr -> EvalST (Bool, Expr)
(e,str) ~> e' = do 
    modify $ (\st -> st{evId = evId st + 1, evSequence = e:evSequence st})
    returnTrace str e (normalizeEval e')


eval :: Knowledge -> Expr -> EvalST (Bool, Expr) 

eval γ e | Just e' <- lookupKnowledge γ e
  = (e, "Knowledge") ~> e' 

eval γ (ELam xs e)
  = do (b, e') <-  eval γ e 
       return (b, ELam xs e')

eval γ (PAtom r e1 e2)
  = do (b1, e1') <- eval γ e1 
       (b2, e2') <- eval γ e2 
       return (b1 || b2, PAtom r e1' e2')

eval γ e@(EIte b e1 e2)
  = do (bb, b') <- eval γ b
       evalIte γ e bb b' e1 e2  

eval γ e@(EApp _ _)
  = do es' <- evalArgs γ e
       fm  <- evFuelMap <$> get 
       evalApp γ fm e es'

eval _ e 
  = return (False, e)


evalArgs :: Knowledge -> Expr -> EvalST (Expr, [Expr], Bool)
evalArgs γ e = go [] False e
  where
    go acc ev (EApp f e)
      = do f' <- eval γ f 
           e' <- eval γ e 
           go (snd e':acc) (fst f' || fst e' || ev) (snd f') 
    go acc ev e 
      = do e' <- eval γ e 
           return (snd e', acc, fst e' || ev)

evalApp :: Knowledge -> FuelMap -> Expr -> (Expr, [Expr],Bool) -> EvalST (Bool, Expr)
evalApp γ _ e (EVar f, [ex], _)
  | (EVar dc, es) <- splitEApp ex
  , Just simp <- L.find (\simp -> (smName simp == f) && (smDC simp == dc)) (knSims γ)
  , length (smArgs simp) == length es 
  = do let e1 = normalizeEval $ substPopIf (zip (smArgs simp) (id <$> es)) (smBody simp) 
       e2    <- eval γ e1
       (e, "Simplify-" ++ showpp f) ~> snd e2

evalApp γ fm e (EVar f, es, evs)
  | Just eq <- L.find ((==f) . eqName) (knAms γ)
  , Just bd <- getEqBody eq 
  , length (eqArgs eq) == length es
  , hasFuel fm f 
  = do let e1   = normalizeEval $  substPopIf (zip (eqArgs eq) es) bd
       putFuelMap $ makeFuelMap (\x -> x-1) fm f
       e2     <- eval γ e1 
       if fst e2 || not (f `elem` syms bd) 
        then (e, "App-" ++ showpp f ++ "\n\n") ~> snd e2
        else return (evs, T.trace ("EVAL STOPPED AS " ++ showpp e2) $ eApps (EVar f) es)


evalApp _ _ _ (f, es, evs)
  = return (evs, eApps f es )


evalIte :: Knowledge -> Expr -> Bool -> Expr -> Expr -> Expr -> EvalST (Bool, Expr)
evalIte γ e _ b e1 _ 
  | isTautoPred b 
  = do e' <- eval γ e1
       (e, "If-True")  ~> (snd e')
evalIte γ e _ b _ e2 
  | isFalse b 
  = do e' <- eval γ e2
       (e, "If-False") ~> (snd e')
evalIte γ _ _ b e1 e2 
  = do e1' <- eval γ e1 
       e2' <- eval γ e2 
       return (False, EIte b (snd e1') (snd e2'))





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
  = KN { knTrues :: [Expr]
       , knFalses ::  [Expr]
       , knSels :: [(Expr, Expr)]
       , knEqs :: [(Expr, Expr)]
       , knSims :: [Simplify]
       , knAms  :: [Equation]
       }

emptyKnowledge :: Knowledge
emptyKnowledge = KN [] [] [] [] [] [] 

lookupKnowledge :: Knowledge -> Expr -> Maybe Expr 
lookupKnowledge γ e 
  | e `elem` (knTrues γ)
  = Just PTrue 
  | e `elem` (knFalses γ)
  = Just PFalse 
  | Just e' <- L.lookup e (knSels γ) 
  = Just e'
  | Just e' <- L.lookup e (knEqs γ)  
  = Just e'
  | otherwise 
  = Nothing 


type EvalST = State EvalEnv

putFuelMap :: FuelMap -> EvalST ()
putFuelMap fm = modify $ \s -> s{evFuelMap = fm}



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

{- 
makeFuelMap' :: (Fuel -> Fuel) -> FuelMap -> Symbol -> FuelMap
makeFuelMap' f fm x = let fm' = makeFuelMap f fm x in  
                      -- T.trace ("New fuel map for " ++ show x ++ "\n OLD = " ++ show (snd <$> fm) ++ "\n NEW = " ++ show (snd <$> fm')) 
                      fm'
-}
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
