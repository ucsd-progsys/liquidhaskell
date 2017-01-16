{-# LANGUAGE ImplicitParams        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE TupleSections         #-}

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

instantiateAxioms :: BindEnv  -> AxiomEnv -> FixSubC -> FixSubC
instantiateAxioms bds aenv sub 
  = let is = instances aenv (pAnd ((expr $ slhs sub):(expr $ srhs sub):(expr . snd <$> envCs bds (senv sub) )))
    in  strengthenLhs {- (traceShow ("LHS = " ++ showpp (slhs sub) ++ "\nRHS = " ++ showpp (srhs sub) ++ "\n\nStrengthened with\n" ++ showExpr is) is) -}
                       is sub

instances :: AxiomEnv -> Expr -> Expr 
instances (AEnv as eqsAll fuel) e 
  = -- traceShow ("FUEL = " ++ show fuel ++"\nExpr = " ++ showpp e ++  "\n INSTANCES = " ++ show (length is) ++ "\n\nINSTANCES = \n\n" ++ showpp is) $ 
    pAnd $ ((eqBody <$> eqsZero) ++ is)
  where
    (eqsZero, eqs) = L.partition (null . eqArgs) eqsAll
    is             = instancesLoop ( (,fuel) <$> as) ( (,fuel) <$> eqs) [e]

-- Currently: Instantiation happens arbitrary times (in recursive functions it diverges)
-- Step 1: Hack it so that instantiation of axiom A happens from an occurences and its 
-- subsequent instances <= FUEL times 
-- How? Hack expressions to contatin fuel info within eg Cst
-- Step 2: Compute fuel based on Ranjit's algorithm

instancesLoop :: [(Symbol, Fuel)] -> [(Equation, Fuel)] -> [Expr] -> [Expr]
instancesLoop as eqs es = go [] (concatMap (makeInitOccurences as eqs) es)
  where 
    go :: [Expr] -> [Occurence] -> [Expr]
    go acc occs = let is      = concatMap (unfold eqs) occs 
                      newIs   = findNewEqs is acc 
                      newOccs = concatMap (grepOccurences eqs) newIs
                  in  if null newIs then acc else go ((fst <$> newIs) ++ acc) newOccs


findNewEqs :: [(Expr, FuelMap)] -> [Expr] -> [(Expr, FuelMap)]
findNewEqs [] _ = []
findNewEqs ((e, f):xss) es 
  | e `elem` es = findNewEqs xss es 
  | otherwise   = (e,f):findNewEqs xss es 

makeInitOccurences :: [(Symbol, Fuel)] -> [(Equation, Fuel)] -> Expr -> [Occurence]
makeInitOccurences xs eqs e 
  = [Occ x es xs | (EVar x, es) <- splitEApp <$> eapps e
                 , (Eq x' xs' _, _) <- eqs, x == x'
                 , length xs' == length es]  

grepOccurences :: [(Equation, Fuel)] -> (Expr, FuelMap) -> [Occurence]
grepOccurences eqs (e, fs) 
  = [Occ x es (makeFuelMap id fs x f) | (EVar x, es) <- splitEApp <$> eapps e
                                      , (Eq x' xs' _, f) <- eqs, x == x'
                                      , length xs' == length es]  

unfold :: [(Equation, Fuel)] -> Occurence -> [(Expr, FuelMap)]
unfold eqs (Occ x es fs) 
  = catMaybes [if hasFuel fs x then Just (subst (mkSubst $ zip  xs' es) e, makeFuelMap (\x -> x-1) fs x f) else Nothing 
              | (Eq x' xs' e, f) <- eqs
              , x == x'
              , length xs' == length es]  

hasFuel :: FuelMap -> Symbol -> Bool 
hasFuel fm x = maybe True (\x -> 0 <= x) (L.lookup x fm)

makeFuelMap :: (Fuel -> Fuel) -> FuelMap -> Symbol -> Fuel -> FuelMap
makeFuelMap _ [] y fy = [(y, fy)] 
makeFuelMap f ((x, fx):fs) y fy 
  | x == y = (x, min (f fx) fy):fs
  | otherwise = (x,fx):fs

data Occurence = Occ {_ofun :: Symbol, _oargs :: [Expr], _ofuel :: FuelMap}
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

