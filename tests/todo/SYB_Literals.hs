{-@ LIQUID "--no-case-expand" @-}
{-# LANGUAGE LambdaCase, DeriveDataTypeable, OverloadedStrings, GeneralizedNewtypeDeriving #-}

import qualified Data.Map as Map
import qualified Data.Generics as SYB
import Data.String
import Text.PrettyPrint

-- Syntax

newtype Var = Var String
  deriving (Eq, Ord, Show, SYB.Data, SYB.Typeable, IsString)

newtype Con = Con String
  deriving (Eq, Ord, Show, SYB.Data, SYB.Typeable, IsString)

type Alts = [(Con, [Var], Expr)]

data Expr
  = EVar Var
  | ELam Var Expr
  | EApp Expr Var
  | ELet [(Var, Expr)] Expr
  | ECon Con [Var]
  | ECase Expr Alts
  deriving (Eq, Ord, Show, SYB.Data, SYB.Typeable)

instance IsString Expr where
  fromString = EVar . fromString

isValue :: Expr -> Bool
isValue = \case
  ELam {} -> True
  ECon {} -> True
  _ -> False

-- Abstract machine
type Heap = Map.Map Var Expr
type Stack = [StackItem]
data StackItem
  = StackUpdate Var
  | StackVar Var
  | StackAlts Alts
  deriving (Show, SYB.Data, SYB.Typeable)
data Machine = Machine Heap Expr Stack
  deriving (Show)

step :: Machine -> Machine
step (Machine heap e stack)
  -- Lookup
  | EVar x <- e =
      let m = heap Map.! x
      in Machine heap m (StackUpdate x : stack)
  -- Update
  | isValue e, StackUpdate v : stack' <- stack =
      Machine (Map.insert v e heap) e stack'
  -- Unwind
  | EApp m x <- e = Machine heap m (StackVar x : stack)
  -- Subst
  | ELam x m <- e, StackVar y : stack' <- stack =
      Machine heap (subst (Map.singleton x y) e) stack'
  -- Case
  | ECase m alts <- e = Machine heap m (StackAlts alts : stack)
  -- Branch
  | ECon con xs <- e, StackAlts alts : stack' <- stack =
      let [(boundVars, body)] = [(boundVars, body) | (con', boundVars, body) <- alts, con == con']
          e' = subst (Map.fromList $ zip boundVars xs) body
      in Machine heap e' stack'
  -- Letrec
  | ELet binds body <- e = Machine (Map.union (Map.fromList binds) heap) body stack

subst :: Map.Map Var Var -> Expr -> Expr
subst sm = \case
  EVar x | Just y <- Map.lookup x sm -> EVar y
  e@(ELam z body) -> ELam z (subst (Map.delete z sm) body)
  e -> SYB.gmapT (SYB.mkT $ subst sm) e

initMachine :: Expr -> Machine
initMachine e = Machine Map.empty e []

isFinished :: Machine -> Bool
isFinished (Machine _ e stack) = isValue e && null stack

run :: Machine -> Machine
run m
  | isFinished m = m
  | otherwise = run $ step m

-- Pretty-printing
ppVar (Var x) = text x
ppCon (Con x) = text x
ppExpr :: Expr -> Doc
ppExpr = ppExpr' False
ppExpr' :: Bool -> Expr -> Doc
ppExpr' p e =
  let maybeParens = if p then parens else id in
  case e of
    EVar x -> ppVar x
    ELam x body -> maybeParens $
      text "λ" <> ppVar x <> text "." <> ppExpr' False body
    EApp a b -> ppExpr' False a <+> ppVar b
    ECon con xs -> sep $ ppCon con : map ppVar xs
    ELet binds body ->
      vcat
        [ "let" $$ nest 2 (vcat (punctuate semi (map (\(v,e) -> ppVar v <+> hang "=" 2 (ppExpr e)) binds)))
        , "in" $$ nest 2 (ppExpr body)
        ]
    ECase e alts ->
      let ppAlt (con, vars, body) =
            ppCon con <+> sep (map ppVar vars) <+> "->" <+> ppExpr body
      in text "case" <+> ppExpr e <+> "of" $$ nest 2 (vcat (map ppAlt alts))

-- Some object-language programs
nil, cons :: Expr
nil = ECon "nil" []
cons = ELam "x" $ ELam "y" $ ECon "cons" ["x", "y"]
append = ELet [("append", appendBind)] "append"
  where
    appendBind =
      ELam "a" $ ELam "b" $ ECase "a"
        [("nil", [], "b")
        ,("cons", ["x", "xs"],
          ELet [("r", "append" `EApp` "xs" `EApp` "b")]
            (cons `EApp` "x" `EApp` "r"))
        ]
