-- Code from: http://www.cs.nott.ac.uk/~pszgmh/ccc2.pdf

{-@ LIQUID "--reflection"     @-}
{- LIQUID "--ple"            @-}
{-@ LIQUID "--no-termination" @-}

module T1812 where

import qualified Data.Set as S 


data Expr = Add Expr Expr | Abs Expr | Var Int 

data Value = Num Int 

data MMaybe a = MJust a | MNothing 

data Type = TInt | TFun Type Type 

{-@ reflect hasType @-}
hasType :: Expr -> MMaybe Type 
hasType (Add e1 e2) 
  = case hasType e1 of 
      MJust TInt -> case hasType e2 of 
                     MJust TInt -> MJust TInt 
                     MNothing   -> MNothing 
      MNothing -> MNothing 
hasType (Abs x) = MNothing 
hasType (Var i) = MNothing 

