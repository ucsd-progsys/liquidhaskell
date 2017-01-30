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


import qualified Data.List as L 
import Data.Maybe (catMaybes)

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
  = strengthenLhs (pAnd ({- is ++ -} trace aenv evalMsg evalEqs)) sub
  where
    _is               = instances maxNumber aenv (trace aenv initMsg $ initOccurences)
    initExpressions  = (expr $ slhs sub):(expr $ srhs sub):(expr <$> binds)
    binds            = envCs bds (senv sub)
    initOccurences   = concatMap (makeInitOccurences as eqs) initExpressions

    as  = (,fuelNumber) . eqName <$> (filter (not . null . eqArgs) $ aenvEqs aenv)
    eqs = aenvEqs  aenv

    evalEqs = [ PAtom F.Eq  e e'| es <- initExpressions, (e, e') <- evaluate (expr <$> binds) as aenv es, e /= e']


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
    evalMsg = "\n\nInit Expr " ++ L.intercalate "\n" (showpp <$> initExpressions) ++
              "\n\nBinds = " ++ showpp binds ++ 
              "\n\nExpressions = " ++ showpp (expr <$> binds) ++ 
              "\n\nShow evalutations " ++ L.intercalate "\n\n" 
                [showpp e ++ "\n -> \n" ++ showpp e' |  es <- initExpressions, (e, e') <- evaluate (expr <$> binds) as aenv es, e /= e']




makeKnowledge :: [Expr] -> ([Expr], [Expr], [(Expr, Expr)])
makeKnowledge es = T.trace ("\n\nMY KNOWLEDGE= \n\n" ++ showpp es ++  "\n\nTRUES = \n\n" ++ showpp tes ++ "\n\nFALSE\n\n" ++ showpp fes ++ "\n\nSELECTORS\n\n" ++ showpp sels) (tes, fes, sels)
  where
    (tes, fes, sels) = mapThd3 concat $ mapSnd3 concat $ mapFst3 concat $ unzip3 (go <$> es)
    go e = let es  = splitPAnd e
               su  = mkSubst [(x, EVar y) | PAtom F.Eq (EVar x) (EVar y) <- es ]
               tes = [e | PIff e t <- es, isTautoPred t] 
               fes = [e | PIff e f <- es, isFalse f ]  
               sels = [(EApp (EVar s) x, e) | PAtom F.Eq (EApp (EVar s) x) e <- es, isSelector s ]
           in (L.nub (tes ++ subst su tes), L.nub (fes ++ subst su fes), L.nub (sels ++ subst su sels))
    splitPAnd (PAnd es) = concatMap splitPAnd es 
    splitPAnd e         = [e]
    isSelector :: Symbol -> Bool 
    isSelector  = L.isPrefixOf "select" . symbolString 
    mapFst3 f (x, y, z) = (f x, y, z)
    mapSnd3 f (x, y, z) = (x, f y, z)
    mapThd3 f (x, y, z) = (x, y, f z)

evaluate :: [Expr] -> FuelMap -> AxiomEnv -> Expr -> [(Expr, Expr)] 
evaluate facts fm aenv einit 
  = concat [evalOne e | e <- L.nub $ grepTopApps einit] 
  where
    (trueExprs, falseExpr, sels) = makeKnowledge facts  
    evalOne e = let e' = go [] (fm, []) (T.trace ("\nSTART EVAL OF\n" ++ showpp e) e) in T.trace ("\n\nEVALUATION OF \n\n" ++ showpp e ++ "\nIS\n" ++ showpp' e') 
                         ((e,) <$> (L.nub $ (fst <$> e')))
    showpp' efs = L.intercalate "\n" [ showpp e ++ "\n" ++ show fm | (e, (fm, _)) <- efs]

    go :: [(Expr, Expr)] -> (FuelMap, [(Expr, [Expr])]) -> Expr -> [(Expr, (FuelMap, [(Expr, [Expr])]))]

    go tr fm e | Just e' <- L.lookup e sels 
      = [(traceEval tr fm "SELECTORYEAH" e e', fm)] 

    go tr fm e@(EApp _ _) -- (EApp e1 e2)
      = evalApp' tr fm [] e -- e1 e2
    go tr fm e@(EIte b e1 e2)
      = do (b', fm1)  <- go tr fm b 
           (e1', fm2) <- go tr fm1 e1
           (e2', fm3) <- go tr fm2 e2 
           return (evalIte tr fm e b' e1' e2', fm3)
    go _ fm e
      = [(e, fm)] 

    evalIte tr fm e b e1 e2 
      | isTautoPred b 
      = normalizeIF $ traceEval tr fm "ifTrue" e e1 
      | isFalse b 
      = normalizeIF $ traceEval tr fm "IfFalse" e e2 
      |  b `elem` trueExprs
      = normalizeIF $ traceEval tr fm "ifTrueYEAH" e e1 
      |  b `elem` falseExpr
      = normalizeIF $ traceEval tr fm "IfFalseYEAH" e e2 
      | otherwise 
      = EIte b e1 e2 

    evalApp' tr fm acc (EApp f e) 
      = do (e', fm1)  <- go tr fm  e 
           (f', fm2)  <- go tr fm1 f 
           (f'', fm3) <- go tr fm  f
           L.nub 
            ( evalApp' tr fm (e:acc) f ++ 
             if e == e' then [] else evalApp' ((e,e'):tr) fm1 (e':acc) f ++ 
             if f == f'' then [] else evalApp' ((f,f''):tr) fm3 (e:acc) f'' ++ 
             if e /= e' && e /= f' then evalApp' ((e,e'):(f,f'):tr) fm2 (e':acc) f' else [] 
             )
    evalApp' tr fm acc e 
      = do (e', fm') <- go tr fm e  
           if e == e' 
             then evalApp ((e,e'):tr) fm' (e', acc) 
             else L.nub (evalApp ((e,e'):tr) fm' (e', acc) ++ evalApp tr fm (e, acc))

    evalApp tr fm (EVar f, [e])
      | (EVar dc, es) <- splitEApp e
      , Just simp <- L.find (\simp -> (smName simp == f) && (smDC simp == dc)) (aenvSimpl aenv)
      , length (smArgs simp) == length es 
      = let e'  = substIfHack (zip (smArgs simp) (id <$> es)) (smBody simp) 
            e'' = traceEval tr fm "Simpl" (eApps (EVar f) [e]) e'
        in map (mapFst normalizeIF) $ go (((eApps (EVar f) [e]), e'):tr) fm e'' 
    evalApp tr fm (EVar f, es)
      | Just eq <- L.find ((==f) . eqName) (aenvEqs aenv)
      , Just bd <- getEqBody eq 
      , length (eqArgs eq) == length es
      , hasFuel (fst fm) f 
      = let e'  = substIfHack (zip (eqArgs eq) (id <$> es)) bd
            e'' = traceEval tr fm ("App-" ++ showpp f) (eApps (EVar f) es) e'
        in map (mapFst normalizeIF) $ go ((eApps (EVar f) es, e'):tr) (mapFst (\fm -> makeFuelMap (\x -> x-1) fm f) fm) e'' 
    evalApp _ fm (e, es) 
      = [(eApps (id e) (id <$> es), fm)]

    mapFst f (x, y) = (f x, y)


    traceEval tr  fm str e1 e2 
      = T.trace ("\nEVAL STEP " ++ str ++ "\nWith fmap" ++ show fm ++ "\n" 
        ++ "\n\nWITH TRACE\n\n" ++ showpp tr  ++ "\n\n"
        ++ showpp e1 ++ "\n -> \n" ++ showpp e2) e2 



substIfHack :: [(Symbol, Expr)] -> Expr -> Expr 
substIfHack xes e = normalizeIF $ foldl go e xes -- subst (mkSubst xes) e  
  where
    go e (x, ex@(EIte b e1 e2)) = let ee = EIte b (subst1 e (x, e1)) (subst1 e (x, e2)) 
                                  in T.trace ("\nSMART SUBST \n" ++ showpp (x, ex) ++ "\nIN\n" ++ showpp e) ee
    go e (x, ex)           = subst1 e (x, ex) 


normalizeIF :: Expr -> Expr  
normalizeIF e = let ne = go e in -- T.trace ("\nNORMALIZED \n" ++ showpp e ++ "\nIS\n" ++ showpp (snd ne)) $ 
                                 snd ne 
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

grepTopApps :: Expr -> [Expr] 
grepTopApps (PAnd es) = concatMap grepTopApps es 
grepTopApps (PAtom _ e1 e2) = (grepTopApps e1) ++ (grepTopApps e2)
grepTopApps e@(EApp _ _) = [e]
grepTopApps _ = [] 


instances :: Int -> AxiomEnv -> [Occurence] -> [Expr] 
instances maxIs aenv !occs 
  = (eqBody <$> eqsZero) ++ is
  where
    (eqsZero, eqs) = L.partition (null . eqArgs) (aenvEqs  aenv)
    is             = instancesLoop aenv maxIs eqs occs

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
