{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Haskell.Liquid.Termination.Structural (terminationVars) where

import Language.Haskell.Liquid.Types hiding (terminationCheck)
import Language.Fixpoint.Types.Errors
import Language.Haskell.Liquid.GHC.Misc (showPpr)
import Language.Haskell.Liquid.UX.Config hiding (terminationCheck)

import CoreSyn
import Var
import Name (getSrcSpan)
import VarSet

import           Text.PrettyPrint.HughesPJ hiding ((<>)) 
import qualified Data.HashSet  as S

terminationVars :: GhcInfo -> [Var]
terminationVars = resultVars . terminationCheck 

resultVars :: Result -> [Var]
resultVars OK         = [] 
resultVars (Error es) = teVar <$> es 

terminationCheck :: GhcInfo -> Result 
terminationCheck info 
  | isStruct  = mconcat $ map (checkBind cbs) (allRecBinds cbs)
  | otherwise = mconcat $ map (checkBind cbs) (S.toList $ gsStTerm $ gsTerm $ giSpec info)
  where 
    isStruct  = structuralTerm   info 
    cbs       = giCbs (giSrc     info)

------------------------------------------------------------------------------------------

data Result = OK | Error [TermError]

data TermError = TE 
  { teVar   :: !Var
  , teError :: !UserError 
  }

mkError :: Var -> Doc -> Result
mkError fun expl = Error [mkTermError fun expl] 

mkTermError :: Var -> Doc -> TermError 
mkTermError fun expl = TE 
  { teVar   = fun 
  , teError = ErrStTerm (getSrcSpan fun) (text $ showPpr fun) expl
  }

instance Monoid Result where
  mempty  = OK
  mappend = (<>)

instance Semigroup Result where
  OK       <> e        = e
  e        <> OK       = e
  Error e1 <> Error e2 = Error (e1 ++ e2)

-- resultToDoc :: Result -> Output Doc
-- resultToDoc OK        = mempty
-- resultToDoc (Error x) = mempty { o_result = Unsafe x }

checkBind :: [CoreBind] -> Var -> Result
checkBind cbs x = maybe OK isStructurallyRecursiveGroup (findRecBind cbs x)

allRecBinds :: [CoreBind] -> [Var]
allRecBinds cbs = concat[ fst <$> xes |  Rec xes <- cbs ]

findRecBind :: [CoreBind] -> Var -> Maybe [(Var,CoreExpr)]
findRecBind [] _ = Nothing
findRecBind (NonRec x _:_) y | x == y
  = Nothing
findRecBind (Rec xes:_)    y | y `elem` (fst <$> xes)
  = Just xes
findRecBind (_:xes) y
  = findRecBind xes y

isStructurallyRecursiveGroup :: [(Var,CoreExpr)] -> Result
isStructurallyRecursiveGroup xes = mconcat (isStructurallyRecursive funs <$> xes)
  where funs = mkVarSet (map fst xes)

isStructurallyRecursive :: VarSet -> (Var, CoreExpr) -> Result
isStructurallyRecursive funs (fun, rhs)
  | null xs
  = mkError fun (text "The definition has no value parameters.")
  | otherwise
  = check (Env (mkError fun) funs (map initParam xs)) [] body
  where
    (_ts, xs, body) = collectTyAndValBinders rhs

data Param = Param
    { origParam :: VarSet -- ^ Variables bound to parameter
    , subterms  :: VarSet -- ^ Variables bound to subterms of the parameter
    }

initParam :: Var -> Param
initParam x = Param (unitVarSet x) emptyVarSet

data Env = Env
    { retErr   :: Doc -> Result -- ^ How to signal erros
    , funs     :: VarSet        -- ^ Which functions are interesting
    , params   :: [Param]       -- ^ Parameters
    }


shadow :: Env -> [Var] -> Env
shadow (Env retErr funs params) vs
    = Env retErr (funs `delVarSetList` vs) (map shadowParam params)
  where
    shadowParam (Param origParam subterms)
      = Param (origParam `delVarSetList` vs) (subterms `delVarSetList` vs)

envAddSubterms :: CoreExpr -- ^ the scrutinee variable
               -> [Var]    -- ^ the variables that are subterms
               -> Env
               -> Env
envAddSubterms (Tick _ e) vs env = envAddSubterms e vs env
envAddSubterms (Cast e _) vs env = envAddSubterms e vs env
envAddSubterms (Var v)    vs env = env { params = map paramAddSubterms (params env) }
  where
    paramAddSubterms p | v `elemVarSet` origParam p || v `elemVarSet` subterms p
                       = p { subterms = subterms p `extendVarSetList` vs }
                       | otherwise = p
envAddSubterms _ _ env = env

check :: Env -> [CoreArg] -> CoreExpr -> Result
check env args = \case
    Var fun | not (fun `elemVarSet` funs env) -> mempty
            | isGoodArgs (params env) args  -> mempty
            | [] <- args -> retErr env $ text "Unsaturated call to" <+> (text $ showPpr fun)
            | otherwise  -> retErr env $ text "Non-structural recursion in call" <+>
                                        (text $ showPpr (mkApps (Var fun) args))

    App e a | isTypeArg a ->                   check env args e
            | otherwise   -> check env [] a <> check env (a:args) e

    Lam v e    -> check (env `shadow` [v]) [] e
    Let (NonRec v rhs) body -> check env  [] rhs <> check (env `shadow` [v]) [] body
    Let (Rec pairs) body -> foldMap (check (env `shadow` vs) []) (body : rhss)
      where (vs,rhss) = unzip pairs

    Case scrut bndr _ alts -> mconcat $
        [ check env [] scrut ] ++
        [ check env' [] rhs
        | (_, pats, rhs) <- alts
        , let env' = envAddSubterms scrut pats $ env `shadow` (bndr:pats) ]

    -- Boring transparent cases
    Cast e _   -> check env args e
    Tick _ e   -> check env args e
    -- Boring base cases
    Lit{}      -> mempty
    Coercion{} -> mempty
    Type{}     -> mempty

-- This is where we check a function call.
-- We go through the list of arguments as long as they are equal
-- to the original parameter. If we find one that is smaller, great. Otherwise,
-- fail.
isGoodArgs :: [Param] -> [CoreArg] -> Bool
isGoodArgs ps     (Cast e _ : as) = isGoodArgs ps (e : as)
isGoodArgs ps     (Tick _ e : as) = isGoodArgs ps (e : as)
isGoodArgs (p:ps) (Var v : as)
    | v `elemVarSet` origParam p = isGoodArgs ps as
    | v `elemVarSet` subterms p  = True -- yay!
isGoodArgs _ _ = False
