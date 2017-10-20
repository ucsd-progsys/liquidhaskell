module Gradual.PrettyPrinting where

import Language.Fixpoint.Types
import Language.Haskell.Liquid.GHC.Misc


class Pretty a where
  pretty :: a -> String 

instance Pretty Expr where
  pretty = showpp . simplifyExpr 

instance Pretty KVar where
  pretty (KV x) = pretty x  

instance Pretty Symbol where
  pretty = show . dropModuleNames. tidySymbol

instance (Pretty a, Pretty b) => Pretty (a, b) where 
  pretty (x,y) = pretty x ++ " |-> " ++ pretty y 

instance (Pretty a) => Pretty [a] where 
  pretty xs = unlines $ map pretty xs 

simplifyExpr :: Expr -> Expr
simplifyExpr = go 
  where
    go (ECst e _)   = go e
    go (EApp e1 e2) 
      | EVar x <- go e1 
      , x `elem` [applyName, toIntName, setToIntName, bitVecToIntName, mapToIntName, realToIntName] 
      = go e2 
    go (EApp e1 e2)
      = EApp (go e1) (go e2)
    go (ENeg e)     = ENeg (go e)
    go (EBin b e1 e2) = EBin b (go e1) (go e2)
    go (EIte e e1 e2) = EIte (go e) (go e1) (go e2)
    go (PAnd es)      = PAnd (go <$> es)
    go (POr es)       = POr (go <$> es)
    go (PNot e)       = PNot (go e)
    go (PImp e1 e2)   = PImp (go e1) (go e2)
    go (PIff e1 e2)   = PIff (go e1) (go e2)
    go (PAtom a e1 e2) = PAtom a  (go e1) (go e2)
    go (PAll a e) = PAll a (go e)
    go (PExist a e) = PExist a (go e)
    go (ETApp e a) = ETApp (go e) a
    go (ELam a e) = ELam a (go e)
    go (EVar x)   = EVar (dropModuleNames $ tidySymbol x)
    go e            = e 
