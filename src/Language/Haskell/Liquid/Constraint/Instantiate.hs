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
-- import qualified Language.Fixpoint.Types as F        
import           Language.Fixpoint.Types.Visitor (eapps)            

import           Language.Haskell.Liquid.Constraint.Types hiding (senv)


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
  = strengthenLhs (pAnd is) sub
  where
    is               = instances maxNumber aenv (trace aenv initMsg $ initOccurences)
    initExpressions  = (expr $ slhs sub):(expr $ srhs sub):(expr <$> envCs bds (senv sub))
    initOccurences   = concatMap (makeInitOccurences as eqs) initExpressions

    as  = (,fuelNumber) . eqName <$> (filter (not . null . eqArgs) $ aenvEqs aenv)
    eqs = aenvEqs  aenv


    showMaybeVar sub   = case subVar sub of 
                           Just x  -> " for " ++ show x
                           Nothing -> "" 

    fuelNumber    = aenvFuel aenv sub 
    initOccNumber = length initOccurences
    axiomNumber   = length $ aenvSyms aenv
    maxNumber     =  (axiomNumber * initOccNumber) ^ fuelNumber
    initMsg = "\nStart instantiation" ++ showMaybeVar sub ++ 
              " with fuel = " ++ show fuelNumber ++ " init occurences = " ++ show initOccNumber ++ " axioms = " ++ show axiomNumber ++ 
              " can generate up to " ++ show maxNumber ++ " instantiations\n"


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
