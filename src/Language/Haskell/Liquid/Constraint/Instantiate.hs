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
import           Language.Fixpoint.Types            
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


instancesLoop :: [Symbol] -> [Equation] -> [Expr] -> [Expr]
instancesLoop as eqs = go []  
  where 
    go acc es = let fes   = concatMap (grepOccurences as) es 
                    is    = concatMap (unfold eqs) $ traceShow "Occurences" fes 
                    newIs = (L.\\) is acc 
                in  if null newIs then acc else go (newIs ++ acc) newIs

      
grepOccurences :: [Symbol] -> Expr -> [Occurence]
grepOccurences xs e = [Occ x es | (EVar x, es) <- splitEApp <$> eapps e, x `elem` xs]  

unfold :: [Equation] -> Occurence -> [Expr]
unfold _ _ = []  


data Occurence = Occ {_ofun :: Symbol, _oargs :: [Expr]}
 deriving (Show)
