{-# LANGUAGE PatternGuards #-}
-- | Eliminate applications of the '?' operator from Core after ANF.
--
-- After ANF, @e ? s@ becomes:
--
-- @
-- let a1 = e
-- let a2 = s
-- ... (?) \@A \@B a1 a2
-- @
--
-- This pass replaces @(?) \@A \@B a1 a2@ with just @a1@, so that no KVars
-- are introduced in the signature of @?@. The binding @a2 = s@ remains in
-- scope, so the lemma's postcondition still enters the environment during
-- constraint generation.

module Language.Haskell.Liquid.Transforms.QuestionMark (eliminateQuestionMark) where

import Liquid.GHC.API as Ghc

-- | Look up the '?' operator in the 'GlobalRdrEnv'. If found, eliminate all
-- its applications from the Core program. If not found (module doesn't import
-- ProofCombinators), return the bindings unchanged.
eliminateQuestionMark :: GlobalRdrEnv -> [CoreBind] -> [CoreBind]
eliminateQuestionMark rdrEnv cbs =
  case lookupQuestionMark rdrEnv of
    Nothing   -> cbs
    Just name -> map (goBind name) cbs

-- | Find the 'Name' of '?' from @Language.Haskell.Liquid.ProofCombinators@
-- in the renamer environment.
lookupQuestionMark :: GlobalRdrEnv -> Maybe Name
lookupQuestionMark rdrEnv =
  case lookupGRE rdrEnv (LookupRdrName rdrName SameNameSpace) of
    [gre] -> Just (greName gre)
    _     -> Nothing
  where
    rdrName = mkRdrQual (mkModuleName "Language.Haskell.Liquid.ProofCombinators")
                        (mkVarOcc "?")

goBind :: Name -> CoreBind -> CoreBind
goBind n (NonRec x e) = NonRec x (goExpr n e)
goBind n (Rec xes)    = Rec [(x, goExpr n e) | (x, e) <- xes]

goExpr :: Name -> CoreExpr -> CoreExpr
goExpr n e
  | Just firstArg <- isQuestionMarkApp n e = goExpr n firstArg
goExpr n (Lam x e)         = Lam x (goExpr n e)
goExpr n (Let b e)          = Let (goBind n b) (goExpr n e)
goExpr n (Case s x t alts) = Case (goExpr n s) x t [goAlt n a | a <- alts]
goExpr n (Cast e co)        = Cast (goExpr n e) co
goExpr n (Tick t e)         = Tick t (goExpr n e)
goExpr n (App f a)          = App (goExpr n f) (goExpr n a)
goExpr _ e                  = e -- Var, Lit, Type, Coercion

goAlt :: Name -> CoreAlt -> CoreAlt
goAlt n (Alt con bs e) = Alt con bs (goExpr n e)

-- | Detect a fully-saturated application of '?': four arguments total
-- (two types + two values), possibly wrapped in ticks.
-- Returns @Just arg1@ (the first value argument).
isQuestionMarkApp :: Name -> CoreExpr -> Maybe CoreExpr
isQuestionMarkApp name expr =
  case collectArgsTicks (const True) expr of
    (Var v, args, _ticks)
      | varName v == name
      , [_tA, _tB, a, _b] <- args
      -> Just a
    _ -> Nothing

