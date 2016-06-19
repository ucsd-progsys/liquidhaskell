module Prover.Pretty where

import Prover.Types

import Language.Fixpoint.Types hiding (Predicate, EApp, EVar, Expr)

instance PPrint (Var a) where
   pprintTidy k = pprintTidy k . var_name

instance PPrint (Expr a) where
   pprintTidy k = pprintTidy k . mkExpr

instance PPrint Predicate where
   pprintTidy k = pprintTidy k . p_pred

instance Show (Axiom a) where
   show a = showpp (axiom_name a) ++ ": " ++ "forall"++ par(sep ", " $ map show (axiom_vars a)) ++ "."  ++ show (axiom_body a) ++ "\n"

instance Show (Instance a) where
   show i = "\nInstance :: " ++ show (inst_axiom i) ++ "With Arguments :: " ++  (sep ", " $ map show (inst_args i))
                       --      ++ "\n\nPredicate = " ++ show (inst_pred i)  ++ "\n\n"

instance Show (Var a) where
   show v = showpp (var_name v) ++ " : " ++ showpp (var_sort v)

instance Show (Ctor a) where
   show c = show (ctor_expr c) ++ "\t \\" ++ (sep ", " $ map show (ctor_vars c)) -- ++ " -> " ++ show (ctor_prop c)

instance Show (VarCtor a) where
   show c = show (vctor_var c) ++ "\t \\" ++ (sep ", " $ map show (vctor_vars c)) --  ++ " -> " ++ show (vctor_prop c)

instance Show (Expr a) where
   show (EVar v)    = showpp v
   show (EApp c es) = show c ++ par (sep ", "  $ map show es)

instance Show Predicate where
   show (Pred p) = showpp $ pprint p

instance Show (Query a) where
   show q = "\nQuery\n" ++
              "\nAxioms::" ++ (showNum $ q_axioms q) ++
              "\nVars  ::" ++ (sep ", " $ map show   $ q_vars   q) ++
              "\nCtors ::" ++ (sep ", " $ map show   $ q_ctors  q) ++
              "\nDecls ::" ++ (sep ", " $ map show   $ q_decls  q) ++
              "\nGoal  ::" ++ (show $ q_goal q) ++
              "\nDecls ::" ++ (show $ q_decls q) ++
              "\nFname ::" ++ (show $ q_fname q)
            where
              showNum ls = concat [ show i ++ " . " ++ show l | (l, i) <- zip ls [1..] ]

instance Show (Proof a) where
  show Invalid    = "\nInvalid\n"
  show (Proof is) = "\nProof ::\n" ++ (sep "\n" $ map show is)


instance Show (ArgExpr a) where
  show ae = "\nArgExpr for " ++ show (arg_sort ae) ++ "\n\nEXPRS = \n\n" ++  (sep ", " (map show $ arg_exprs ae)) ++
            "\n\nConstructors = " ++ (sep ", " (map show $ arg_ctors ae)) ++ "\n\n"


par :: String -> String
par str = " (" ++ str ++ ") "

sep :: String -> [String] -> String
sep _ []     = []
sep _ [x]    = x
sep c (x:xs) = x ++ c ++ sep c xs
