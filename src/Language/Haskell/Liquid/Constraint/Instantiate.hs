{-# LANGUAGE ImplicitParams        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE EmptyDataDecls        #-}

--------------------------------------------------------------------------------
-- | Axiom Instantiation  ------------------------------------------------------
--------------------------------------------------------------------------------

module Language.Haskell.Liquid.Constraint.Instantiate (

  instantiateAxioms

  ) where


import           Language.Fixpoint.Misc            
import           Language.Fixpoint.Types hiding (Eq)
import qualified Language.Fixpoint.Types as F        
import           Language.Fixpoint.Types.Visitor (eapps)            
-- import           Language.Haskell.Liquid.Types

import           Language.Haskell.Liquid.Constraint.Types


import qualified Data.List as L 

instantiateAxioms :: AxiomEnv -> FixSubC -> FixSubC
instantiateAxioms aenv sub 
  = let is = instances aenv (pAnd [expr $ slhs sub, expr $ srhs sub])
    in  strengthenLhs (traceShow ("LHS = " ++ showpp (slhs sub) ++ "\nRHS = " ++ showpp (slhs sub)) is)
                       sub

instances :: AxiomEnv -> Expr -> Expr 
instances (AEnv as eqs) e = pAnd $ instancesLoop as eqs [e]

-- Currently: Instantiation happens arbitrary times (in recursive functions it diverges)
-- Step 1: Hack it so that instantiation of axiom A happens from an occurences and its 
-- subsequent instances <= FUEL times 
-- How? Hack expressions to contatin fuel info within eg Cst s
-- Step 2: Compute fuel based on Ranjit's algorithm

instancesLoop :: [Symbol] -> [Equation] -> [Expr] -> [Expr]
instancesLoop as eqs = go []  
  where 
    go acc es = let fes   = concatMap (grepOccurences as) es 
                    is    = traceShow "Instances" $ concatMap (unfold eqs) $ traceShow "Occurences" fes 
                    newIs = traceShow "NewInstances" $ (L.\\) is acc 
                in  if null newIs then acc else go (newIs ++ acc) newIs

      
grepOccurences :: [Symbol] -> Expr -> [Occurence]
grepOccurences xs e = [Occ x es | (EVar x, es) <- splitEApp <$> eapps e, x `elem` xs]  

unfold :: [Equation] -> Occurence -> [Expr]
unfold eqs (Occ x es) = [PAtom F.Eq (eApps (EVar x) es) (subst (mkSubst $ zip  xs' es) e) | (Eq x' xs' e) <- eqs, x == x']  


data Occurence = Occ {_ofun :: Symbol, _oargs :: [Expr]}
 deriving (Show)
