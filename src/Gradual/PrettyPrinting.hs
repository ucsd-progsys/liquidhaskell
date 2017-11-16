module Gradual.PrettyPrinting where

import Language.Fixpoint.Types
import Language.Haskell.Liquid.GHC.Misc


class Pretty a where
  pretty :: a -> String 

instance Pretty Expr where
  pretty = showpp . simplifyExpr 

instance Pretty KVar where
  pretty (KV x) = pretty x  

instance Pretty SortedReft where
  pretty (RR s (Reft (x,e))) = "{ " ++ pretty x ++ " : " ++ pretty s ++ " | " ++ pretty e ++ "}"

instance Pretty Sort where
  pretty FInt          = "Int"
  pretty FReal         = "Real"
  pretty FNum          = "Num"
  pretty FFrac         = "FFrac"
  pretty (FObj x)      = pretty x 
  pretty (FVar v)      = "@" ++ pretty v
  pretty (FFunc s1 s2) = pretty s1 ++ " -> " ++ pretty s2
  pretty (FAbs i s)    = "forall " ++ pretty i ++ "." ++ pretty s
  pretty (FTC tc)      = pretty (symbol tc)
  pretty (FApp s1 s2)  = pretty s1 ++ " " ++ pretty s2

instance Pretty Int where
  pretty = show

instance (Pretty a, Pretty b, Pretty c) =>  Pretty (a, b, c) where
  pretty (x, y, z) = "(" ++ pretty x ++ "," ++ pretty y ++ "," ++ pretty z ++ ")" 

instance Pretty Symbol where
  pretty = show . dropModuleNames. tidySymbol

instance (Pretty a, Pretty b) => Pretty (a, b) where 
  pretty (x,y) = pretty x ++ " |-> " ++ pretty y 

instance (Pretty a) => Pretty [a] where 
  pretty xs = unlines $ map pretty xs 

instance Pretty () where
  pretty () = "" 

instance Pretty a => Pretty (Maybe a) where
  pretty Nothing  = "Nothing"
  pretty (Just x) = "Just" ++ pretty x  

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
    go (PAll bs e)     = PAll   [ (goSym x, s) | (x,s) <- bs] (go e)
    go (PExist bs e)   = PExist [ (goSym x, s) | (x,s) <- bs] (go e)
    go (ETApp e a) = ETApp (go e) a
    go (ELam a e) = ELam a (go e)
    go (EVar x)   = EVar (goSym x)
    go e            = e 
    goSym = dropModuleNames . tidySymbol



showCs :: BindEnv -> SimpC a -> String 
showCs env cs = 
  "CS = " ++ show (_cid cs) ++ 
  unlines (pretty <$> e) ++ 
  "\n => \n" ++ 
  (pretty $ _crhs cs)
  where
    e = [(i, x, e) | (i, x, e) <-  bindEnvToList env
                   , i `elem` elemsIBindEnv (_cenv cs)]
