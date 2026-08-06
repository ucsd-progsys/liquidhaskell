{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
-- | Eliminate applications of the '?' operator and 'const' from Core after ANF.
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
--
-- This pass fixes #2544.
--
-- Eliminating applications of 'const' is convenient when importing modules from
-- liquid-prelude is unwanted and therefore `?` is unavailable.

module Language.Haskell.Liquid.Transforms.QuestionMark (eliminateQuestionMark) where

import qualified Language.Haskell.TH.Syntax as TH (nameModule)
import Liquid.GHC.API as Ghc

-- | Look up the 'FunctionNames' in the 'GlobalRdrEnv'. If found, eliminate all
-- their applications from the Core program. If not found, return the bindings unchanged.
eliminateQuestionMark :: GlobalRdrEnv -> [CoreBind] -> [CoreBind]
eliminateQuestionMark rdrEnv cbs =
  case lookupFunctionNames rdrEnv of
    Nothing    -> cbs
    Just names -> map (goBind names) cbs
-- | A record of function names whose applications are to be removed form the core program.
data FunctionNames = FunctionNames
  { questionMarkName :: Maybe Name
  , constName        :: Maybe Name
  }

lookupFunctionNames :: GlobalRdrEnv -> Maybe FunctionNames
lookupFunctionNames rdrEnv =
  case (lookupQuestionMark rdrEnv, lookupConst rdrEnv) of
    (Nothing, Nothing) -> Nothing
    (n0, n1) -> Just (FunctionNames n0 n1)

-- | Find the 'Name' of '?' from @Language.Haskell.Liquid.ProofCombinators@
-- in the renamer environment.
lookupQuestionMark :: GlobalRdrEnv -> Maybe Name
lookupQuestionMark rdrEnv =
  let m = "Language.Haskell.Liquid.ProofCombinators"
   in case filter (nameModuleIs m . greName) $
             lookupGRE rdrEnv (LookupOccName (mkVarOcc "?") SameNameSpace) of
        [gre] -> Just (greName gre)
        _     -> Nothing

-- | Find the 'Name' of 'const' from @base@ in the renamer environment.
lookupConst :: GlobalRdrEnv -> Maybe Name
lookupConst rdrEnv = do
  m <- TH.nameModule 'const
  case filter (nameModuleIs m . greName) $
         lookupGRE rdrEnv (LookupOccName (mkVarOcc "const") SameNameSpace) of
    [gre] -> do
      Just (greName gre)
    _     -> Nothing

nameModuleIs :: String -> Name -> Bool
nameModuleIs m n = case nameModule_maybe n of
  Just m' -> moduleNameString (moduleName m') == m
  Nothing -> False

goBind :: FunctionNames -> CoreBind -> CoreBind
goBind n (NonRec x e) = NonRec x (goExpr n e)
goBind n (Rec xes)    = Rec [(x, goExpr n e) | (x, e) <- xes]

goExpr :: FunctionNames -> CoreExpr -> CoreExpr
goExpr n e
  | Just qmName <- questionMarkName n
  , Just firstArg <- isQuestionMarkApp qmName e =
      goExpr n firstArg
  | Just cName <- constName n
  , Just firstArg <- isQuestionMarkApp cName e =
      goExpr n firstArg
goExpr n (Lam x e)         = Lam x (goExpr n e)
goExpr n (Let b e)          = Let (goBind n b) (goExpr n e)
goExpr n (Case s x t alts) = Case (goExpr n s) x t [goAlt n a | a <- alts]
goExpr n (Cast e co)        = Cast (goExpr n e) co
goExpr n (Tick t e)         = Tick t (goExpr n e)
goExpr n (App f a)          = App (goExpr n f) (goExpr n a)
goExpr _ e                  = e -- Var, Lit, Type, Coercion

goAlt :: FunctionNames -> CoreAlt -> CoreAlt
goAlt n (Alt con bs e) = Alt con bs (goExpr n e)

-- | Detect a fully-saturated application of '?' or `const`: four arguments total
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

