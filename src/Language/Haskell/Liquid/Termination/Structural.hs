{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric       #-}

module Language.Haskell.Liquid.Termination.Structural (terminationVars) where

import Language.Haskell.Liquid.Types hiding (terminationCheck)
import Language.Haskell.Liquid.GHC.Misc (showPpr)
-- import Language.Haskell.Liquid.UX.Config hiding (terminationCheck)

import CoreSyn
import Var
import Name (getSrcSpan)
import VarSet

import           Text.PrettyPrint.HughesPJ hiding ((<>)) 
import qualified Data.HashSet  as S
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import Data.Maybe (mapMaybe)

terminationVars :: GhcInfo -> [Var]
terminationVars = resultVars . terminationCheck

resultVars :: Result a -> [Var]
resultVars (OK _)       = []
resultVars (Error es) = teVar <$> es 

terminationCheck :: GhcInfo -> Result ()
terminationCheck info 
  | isStruct  = mconcat $ map (checkBind cbs) (allRecBinds cbs)
  | otherwise = mconcat $ map (checkBind cbs) (S.toList $ gsStTerm $ gsTerm $ giSpec info)
  where 
    isStruct  = structuralTerm   info 
    cbs       = giCbs (giSrc     info)

------------------------------------------------------------------------------------------

data Result a = OK a | Error [TermError]

data TermError = TE 
  { teVar   :: !Var
  , teError :: !UserError 
  }

mkError :: Var -> Doc -> Result a
mkError fun expl = Error [mkTermError fun expl] 

mkTermError :: Var -> Doc -> TermError
mkTermError fun expl = TE 
  { teVar   = fun 
  , teError = ErrStTerm (getSrcSpan fun) (text $ showPpr fun) expl
  }

instance Monoid a => Monoid (Result a) where
  mempty  = OK mempty
  mappend = (<>)

instance Semigroup a => Semigroup (Result a) where
  OK x     <> OK y     = OK (x <> y)
  OK _     <> e        = e
  e        <> OK _     = e
  Error e1 <> Error e2 = Error (e1 ++ e2)

-- resultToDoc :: Result -> Output Doc
-- resultToDoc OK        = mempty
-- resultToDoc (Error x) = mempty { o_result = Unsafe x }

checkBind :: [CoreBind] -> Var -> Result ()
checkBind cbs x = maybe (OK ()) isStructurallyRecursiveGroup (findRecBind cbs x)

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

isStructurallyRecursiveGroup :: [(Var,CoreExpr)] -> Result ()
isStructurallyRecursiveGroup xes = mconcat (isStructurallyRecursive funs <$> xes)
  where funs = mkVarSet (map fst xes)

isStructurallyRecursive :: VarSet -> (Var, CoreExpr) -> Result ()
isStructurallyRecursive funs (fun, rhs)
  | null xs
  = mkError fun (text "The definition has no value parameters.")
  | otherwise
  = let env = Env (mkError fun) funs (map initParam xs) in
      case check env [] body of
        OK calls -> structDecreasing env calls
        Error err -> Error err
  where
    (_ts, xs, body) = collectTyAndValBinders rhs

data Param = Param
    { origParam :: VarSet -- ^ Variables bound to parameter
    , subterms  :: VarSet -- ^ Variables bound to subterms of the parameter
    }

initParam :: Var -> Param
initParam x = Param (unitVarSet x) emptyVarSet

data Env a = Env
    { retErr   :: Doc -> Result a  -- ^ How to signal erros
    , funs     :: VarSet           -- ^ Which functions are interesting
    , params   :: [Param]          -- ^ Parameters
    }


shadow :: Env a -> [Var] -> Env a
shadow (Env retErr funs params) vs
    = Env retErr (funs `delVarSetList` vs) (map shadowParam params)
  where
    shadowParam (Param origParam subterms)
      = Param (origParam `delVarSetList` vs) (subterms `delVarSetList` vs)

envAddSubterms :: CoreExpr -- ^ the scrutinee variable
               -> [Var]    -- ^ the variables that are subterms
               -> Env a
               -> Env a
envAddSubterms (Tick _ e) vs env = envAddSubterms e vs env
envAddSubterms (Cast e _) vs env = envAddSubterms e vs env
envAddSubterms (Var v)    vs env = env { params = map paramAddSubterms (params env) }
  where
    paramAddSubterms p | v `elemVarSet` origParam p || v `elemVarSet` subterms p
                       = p { subterms = subterms p `extendVarSetList` vs }
                       | otherwise = p
envAddSubterms _ _ env = env

check :: Env (S.HashSet Call) -> [CoreArg] -> CoreExpr -> Result (S.HashSet Call)
check env args = \case
    Var fun | not (fun `elemVarSet` funs env) -> mempty
            | length args < length (params env) -> retErr env $ text "Unsaturated call to" <+> (text $ showPpr fun)
            | otherwise -> OK $ S.singleton $ getStructArgs (showPpr $ mkApps (Var fun) args) $ zip (params env) args

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

data Call = Call
  { callSource :: String
  , candidateArgs :: S.HashSet Int
  , decreasingArgs :: S.HashSet Int
  } deriving (Eq, Show, Generic)

instance Hashable Call

-- This is where we  check a function call. We go through  the list of arguments
-- and find the  indices of those which are decreasing.  Note that this approach
-- is only guaranteed to  work when the arguments to the  function are named, so
-- e.g.
-- foo (x:xs) (y:ys) = foo xs (y:ys)
-- won't necessarily work, but
-- foo (x:xs) yys@(y:ys) = foo xs yys
-- will.
getStructArgs :: String -> [(Param, CoreArg)] -> Call
getStructArgs src args =
  let (ca, da) = getStructArgs' 0 args in Call src ca da
  where
    getStructArgs' _ [] = (S.empty, S.empty)
    getStructArgs' i ((p, Cast e _) : args) = getStructArgs' i ((p, e) : args)
    getStructArgs' i ((p, Tick _ e) : args) = getStructArgs' i ((p, e) : args)
    getStructArgs' i ((p, Var v) : args)
      | v `elemVarSet` origParam p = (S.singleton i, S.empty) <> getStructArgs' (i + 1) args
      | v `elemVarSet` subterms p = (S.singleton i, S.singleton i) <> getStructArgs' (i + 1) args
      | otherwise = getStructArgs' (i + 1) args
    getStructArgs' i (_ : args) = getStructArgs' (i + 1) args

-- Check if there is some way to lexicographically order the arguments so that
-- they are structurally decreasing. Essentially, in order for there to be, we
-- must be able to find some argument which is always either unchanged or
-- decreasing. We can then remove every call where that argument is decreasing
-- and recurse.
structDecreasing :: Env () -> S.HashSet Call -> Result ()
structDecreasing env calls
  | S.null calls = mempty
  | not $ S.null nonDecCalls = raiseErr nonDecCalls
  | otherwise =
      let ca = commonArgs calls in
        if S.null ca then
          raiseErr calls
        else
          structDecreasing env $ (S.fromList . mapMaybe (removeDecreasing ca) . S.toList) calls
  where
    raiseErr calls =
      retErr env $ text "Non-structural recursion in calls" <+>
      (text $ showPpr (S.map callSource calls))
    nonDecCalls = S.filter (S.null . decreasingArgs) calls
    commonArgs calls = foldl1 S.intersection (S.map candidateArgs calls)
    removeDecreasing args call
      | S.null (decreasingArgs call `S.difference` args) = Nothing
      | otherwise = Just $ call
        { candidateArgs = candidateArgs call `S.difference` args
        , decreasingArgs = decreasingArgs call `S.difference` args
        }
