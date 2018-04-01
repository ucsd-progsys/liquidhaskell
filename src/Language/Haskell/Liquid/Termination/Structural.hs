{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Haskell.Liquid.Termination.Structural (

  terminationCheck

  ) where 

import Language.Haskell.Liquid.Types hiding (terminationCheck)
import Language.Fixpoint.Types.Errors
import Language.Haskell.Liquid.GHC.Misc (showPpr)

import CoreSyn
import Var
import Name (getSrcSpan)
import VarSet
import UniqSet (nonDetEltsUniqSet)
import Data.Monoid ((<>))

import Text.PrettyPrint.HughesPJ hiding ((<>))
import qualified Data.HashSet                           as S


terminationCheck :: GhcInfo -> Output Doc 
terminationCheck info = mconcat $ map (resultToDoc . checkBind (cbs info)) (S.toList $ gsStTerm $ spec info)


data Result = OK | Error [UserError] 

instance Monoid Result where
  mempty = OK 
  mappend OK e = e 
  mappend e OK = e 
  mappend (Error e1) (Error e2) = Error (e1 ++ e2)

resultToDoc :: Result -> Output Doc 
resultToDoc OK        = mempty
resultToDoc (Error x) = mempty {o_result = Unsafe x }

checkBind :: [CoreBind] -> Var -> Result
checkBind cbs x = maybe OK isStructurallyRecursiveGroup (findRecBind cbs x)


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
  = check (Env (mkError fun) funs (mkVarSet xs) emptyVarSet) body
  where
    (_ts, xs, body) = collectTyAndValBinders rhs

mkError :: Var -> Doc -> Result
mkError fun expl = Error [ErrStTerm (getSrcSpan fun) (text $ showPpr fun) expl]

data Env = Env
    { retErr   :: Doc -> Result -- ^ How to signal erros
    , funs     :: VarSet        -- ^ Which functions are interesting
    , params   :: VarSet        -- ^ Variables bound to the first parameter of the current function
    , subterms :: VarSet        -- ^ Variables bound to immediate subterms of these parameters
    }

shadow :: Env -> [Var] -> Env
shadow (Env retErr funs params subterms) vs
    = Env retErr (funs `delVarSetList` vs) (params `delVarSetList` vs) (subterms `delVarSetList` vs)

envAddSubterms :: Env -> [Var] -> Env
envAddSubterms env vs = env { subterms = subterms env `extendVarSetList` vs }

check :: Env -> CoreExpr -> Result
check env = \case
    e@Var{}    -> checkCall env (collectArgs e)
    e@App{}    -> checkCall env (collectArgs e)
    Lam v e    -> check (env `shadow` [v]) e
    Let (NonRec v rhs) body -> check env rhs <> check (env `shadow` [v]) body
    Let (Rec pairs) body -> foldMap (check (env `shadow` vs)) (body : rhss)
      where (vs,rhss) = unzip pairs

    Case scrut bndr _ alts -> mconcat $
        [ check env scrut ] ++
        [ let env' | isParam env scrut = env `shadow` (bndr:pats) `envAddSubterms` pats
                   | otherwise         = env `shadow` (bndr:pats)
          in check env' rhs
        | (_, pats, rhs) <- alts]

    -- Boring transparent cases
    Cast e _   -> check env e
    Tick _ e   -> check env e
    -- Boring base cases
    Lit{}      -> mempty
    Coercion{} -> mempty
    Type{}     -> mempty

isParam :: Env -> CoreExpr -> Bool
isParam env (Var v)    = v `elemVarSet` params env
isParam env (Cast e _) = isParam env e
isParam env (Tick _ e) = isParam env e
isParam _   _          = False

isGoodArg :: Env -> CoreExpr -> Bool
isGoodArg env (Var v)    = v `elemVarSet` subterms env
isGoodArg env (Cast e _) = isGoodArg env e
isGoodArg env (Tick _ e) = isGoodArg env e
isGoodArg _   _          = False

checkCall :: Env -> (CoreExpr, [CoreExpr]) -> Result
checkCall env (Var fun, args)
    | not (fun `elemVarSet` funs env)
    = checkArgs
    | null args
    = retErr env $ text "Unsaturated call to" <+> (text $ showPpr fun)
    | isGoodArg env firstArg
    = checkArgs
    | otherwise =
    retErr env $ text "Non-structural recursion in call" <+> (text $ showPpr (App (Var fun) firstArg)) $$ subTermsHelpMsg
  where
    valArgs   = dropWhile isTypeArg args
    firstArg  = head valArgs
    checkArgs = foldMap (check env) args

    subTermsHelpMsg | isEmptyVarSet (subterms env) = text "No valid arguments are in scope."
                    | otherwise = text "Valid arguments are: " <+> (hcat $ punctuate comma $ map (text . showPpr) $ nonDetEltsUniqSet (subterms env))

-- Not a variable in the function position
checkCall env (e, args) = foldMap (check env) (e : args)


