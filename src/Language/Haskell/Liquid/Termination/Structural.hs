{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

module Language.Haskell.Liquid.Termination.Structural (terminationVars) where

import Language.Haskell.Liquid.Types hiding (terminationCheck, isDecreasing, GhcInfo(..), GhcSrc(..), GhcSpec(..))
import Language.Haskell.Liquid.Types.SpecDesign
import Language.Haskell.Liquid.GHC.Misc (showPpr)

import CoreSyn
import Var
import Name (getSrcSpan)
import VarSet
import CoreSubst (deShadowBinds)

import Text.PrettyPrint.HughesPJ hiding ((<>))

import qualified Data.HashSet as HS
import Data.HashSet (HashSet)
import qualified Data.Map.Strict as M
import Data.Map.Strict (Map)
import qualified Data.List as L

import Control.Monad (liftM, ap)
import Data.Foldable (fold)

terminationVars :: TargetInfo -> [Var]
terminationVars info = failingBinds info >>= allBoundVars

failingBinds :: TargetInfo -> [CoreBind]
failingBinds info = filter (hasErrors . checkBind) structBinds
  where 
    structCheckWholeProgram = structuralTerm info
    program = giCbs . giSrc $ info
    structFuns = gsStTerm . gsTerm . giSpec $ info
    structBinds
      | structCheckWholeProgram = program
      | otherwise = findStructBinds structFuns program

checkBind :: CoreBind -> Result ()
checkBind bind = do
  srcCallInfo <- getCallInfoBind emptyEnv (deShadowBind bind)
  let structCallInfo = fmap toStructCall <$> srcCallInfo
  fold $ mapWithFun structDecreasing structCallInfo

deShadowBind :: CoreBind -> CoreBind
deShadowBind bind = head $ deShadowBinds [bind]

findStructBinds :: HashSet Var -> CoreProgram -> [CoreBind]
findStructBinds structFuns program = filter isStructBind program
  where
    isStructBind (NonRec f _) = f `HS.member` structFuns
    isStructBind (Rec []) = False
    isStructBind (Rec ((f,_):xs)) = f `HS.member` structFuns || isStructBind (Rec xs)

allBoundVars :: CoreBind -> [Var]
allBoundVars (NonRec v e) = v : (nextBinds e >>= allBoundVars)
allBoundVars (Rec binds) = map fst binds ++ (map snd binds >>= nextBinds >>= allBoundVars)

nextBinds :: CoreExpr -> [CoreBind]
nextBinds = \case
  App e a -> nextBinds e ++ nextBinds a
  Lam _ e -> nextBinds e
  Let b e -> [b] ++ nextBinds e
  Case scrut _ _ alts -> nextBinds scrut ++ ([body | (_, _, body) <- alts] >>= nextBinds)
  Cast e _ -> nextBinds e
  Tick _ e -> nextBinds e
  Var{} -> []
  Lit{} -> []
  Coercion{} -> []
  Type{} -> []

------------------------------------------------------------------------------------------

-- Note that this is *not* the Either/Maybe monad, since it's important that we
-- collect all errors, not just the first error.
data Result a = Result
  { resultVal :: a
  , resultErrors :: [TermError]
  } deriving (Show)

data TermError = TE 
  { teVar   :: Var
  , teError :: UserError
  } deriving (Show)

hasErrors :: Result a -> Bool
hasErrors = not . null . resultErrors

addError :: Var -> Doc -> Result a -> Result a
addError fun expl (Result x errs) = Result x (mkTermError fun expl : errs)

mkTermError :: Var -> Doc -> TermError
mkTermError fun expl = TE
  { teVar   = fun
  , teError = ErrStTerm (getSrcSpan fun) (text $ showPpr fun) expl
  }

instance Monoid a => Monoid (Result a) where
  mempty  = Result mempty []

instance Semigroup a => Semigroup (Result a) where
  Result x e1 <> Result y e2 = Result (x <> y) (e1 ++ e2)

instance Monad Result where
  Result x e1 >>= f =
    let Result y e2 = f x in
    Result y (e2 ++ e1)

instance Applicative Result where
  pure x = Result x []
  (<*>) = ap

instance Functor Result where
  fmap = liftM

--------------------------------------------------------------------------------

data Env = Env
  { envCurrentFun :: Maybe Var
  , envCurrentArgs :: [CoreArg]
  , envCheckedFuns :: [Fun]
  }

data Fun = Fun
  { funName :: Var
  , funParams :: [Param]
  }

data Param = Param
  { paramNames :: VarSet
  , paramSubterms :: VarSet
  } deriving (Eq)

emptyEnv :: Env
emptyEnv = Env
  { envCurrentFun = Nothing
  , envCurrentArgs = []
  , envCheckedFuns = []
  }

mkFun :: Var -> Fun
mkFun name = Fun
  { funName = name
  , funParams = []
  }

mkParam :: Var -> Param
mkParam name = Param
  { paramNames = unitVarSet name
  , paramSubterms = emptyVarSet
  }

lookupFun :: Env -> Var -> Maybe Fun
lookupFun env name = L.find (\fun -> funName fun == name) $ envCheckedFuns env

clearCurrentArgs :: Env -> Env
clearCurrentArgs env = env { envCurrentArgs = [] }

setCurrentFun :: Var -> Env -> Env
setCurrentFun fun env = env { envCurrentFun = Just fun }

clearCurrentFun :: Env -> Env
clearCurrentFun env = env { envCurrentFun = Nothing }

addArg :: CoreArg -> Env -> Env
addArg arg env = env { envCurrentArgs = arg:envCurrentArgs env }

addParam :: Var -> Env -> Env
addParam param env = case envCurrentFun env of
  Nothing -> env
  Just name -> env { envCheckedFuns = updateFunNamed name <$> envCheckedFuns env }
  where
    updateFunNamed name fun
      | funName fun == name = fun { funParams = mkParam param : funParams fun }
      | otherwise = fun

addSynonym :: Var -> Var -> Env -> Env
addSynonym oldName newName env = env { envCheckedFuns = updateFun <$> envCheckedFuns env }
  where
    updateFun fun = fun { funParams = updateParam <$> funParams fun }
    updateParam param
      | oldName `elemVarSet` paramNames param = param { paramNames = paramNames param `extendVarSet` newName }
      | oldName `elemVarSet` paramSubterms param = param { paramSubterms = paramSubterms param `extendVarSet` newName }
      | otherwise = param

addSubterms :: Var -> [Var] -> Env -> Env
addSubterms var subterms env = env { envCheckedFuns = updateFun <$> envCheckedFuns env }
  where
    updateFun fun = fun { funParams = updateParam <$> funParams fun }
    updateParam param
      | var `elemVarSet` paramNames param || var `elemVarSet` paramSubterms param = param { paramSubterms = paramSubterms param `extendVarSetList` subterms }
      | otherwise = param

addCheckedFun :: Var -> Env -> Env
addCheckedFun name env = env { envCheckedFuns = mkFun name : envCheckedFuns env }

isParam :: Var -> Param -> Bool
var `isParam` param = var `elemVarSet` paramNames param

isParamSubterm :: Var -> Param -> Bool
var `isParamSubterm` param = var `elemVarSet` paramSubterms param

--------------------------------------------------------------------------------

newtype FunInfo a = FunInfo (Map Var a)

data SrcCall = SrcCall
  { srcCallFun :: Var
  , srcCallArgs :: [(Param, CoreArg)]
  }

instance Semigroup a => Semigroup (FunInfo a) where
  FunInfo xs <> FunInfo ys = FunInfo $ M.unionWith (<>) xs ys

instance Semigroup a => Monoid (FunInfo a) where
  mempty = FunInfo M.empty

instance Functor FunInfo where
  fmap f (FunInfo xs) = FunInfo (fmap f xs)

instance Foldable FunInfo where
  foldMap f (FunInfo m) = foldMap f m

mapWithFun :: (Var -> a -> b) -> FunInfo a -> FunInfo b
mapWithFun f (FunInfo x) = FunInfo (M.mapWithKey f x)

mkFunInfo :: Var -> a -> FunInfo a
mkFunInfo fun x = FunInfo $ M.singleton fun x

mkSrcCall :: Var -> [(Param, CoreArg)] -> SrcCall
mkSrcCall fun args = SrcCall
  { srcCallFun = fun
  , srcCallArgs = args
  }

toVar :: CoreExpr -> Maybe Var
toVar (Var x) = Just x
toVar (Cast e _) = toVar e
toVar (Tick _ e) = toVar e
toVar _ = Nothing

zipExact :: [a] -> [b] -> Maybe [(a, b)]
zipExact [] [] = Just []
zipExact (x:xs) (y:ys) = ((x, y):) <$> zipExact xs ys
zipExact _ _ = Nothing

-- Collect information about all of the recursive calls in a function
-- definition which will be needed to check for structural termination.
getCallInfoExpr :: Env -> CoreExpr -> Result (FunInfo [SrcCall])
getCallInfoExpr env = \case
  Var (lookupFun env -> Just fun) ->
    case zipExact (funParams fun) (reverse $ envCurrentArgs env) of
      Just args -> pure $ mkFunInfo (funName fun) [mkSrcCall (funName fun) args]
      Nothing -> addError (funName fun) "Unsaturated call to function" mempty

  App e a
    | isTypeArg a -> getCallInfoExpr env e
    | otherwise -> getCallInfoExpr argEnv a <> getCallInfoExpr appEnv e
      where
        argEnv = clearCurrentFun . clearCurrentArgs $ env
        appEnv = clearCurrentFun . addArg a $ env

  Lam x e
    | isTyVar x -> getCallInfoExpr env e
    | otherwise -> getCallInfoExpr (addParam x env) e

  Let bind e -> getCallInfoBind env bind <> getCallInfoExpr env e

  Case (toVar -> Just var) bndr _ alts -> foldMap getCallInfoAlt alts
    where
      getCallInfoAlt (_, subterms, body) = getCallInfoExpr (branchEnv subterms) body
      branchEnv subterms = addSubterms var subterms . addSynonym var bndr $ env

  Case scrut _ _ alts -> getCallInfoExpr env scrut <> foldMap getCallInfoAlt alts
    where
      getCallInfoAlt (_, _, body) = getCallInfoExpr env body

  Cast e _ -> getCallInfoExpr env e
  Tick _ e -> getCallInfoExpr env e

  Var{} -> pure mempty
  Lit{} -> pure mempty
  Coercion{} -> pure mempty
  Type{} -> pure mempty

getCallInfoBind :: Env -> CoreBind -> Result (FunInfo [SrcCall])
getCallInfoBind env = \case
  NonRec _ e -> getCallInfoExpr (clearCurrentFun env) e
  Rec [] -> pure mempty
  Rec [(f, e)] -> getCallInfoExpr (addCheckedFun f . setCurrentFun f $ env) e
  Rec binds -> foldMap failBind binds
    where failBind (f, e) =
            addError f "Structural checking of mutually-recursive functions is not supported" $
            getCallInfoExpr (clearCurrentFun env) e

--------------------------------------------------------------------------------

data StructInfo = Unchanged Int | Decreasing Int

unStructInfo :: StructInfo -> Int
unStructInfo (Unchanged p) = p
unStructInfo (Decreasing p) = p

isDecreasing :: StructInfo -> Bool
isDecreasing (Decreasing _) = True
isDecreasing (Unchanged _) = False

data StructCall = StructCall
  { structCallFun :: Var
  , structCallArgs :: [Int]
  , structCallDecArgs :: [Int]
  }

mkStructCall :: Var -> [StructInfo] -> StructCall
mkStructCall fun sis = StructCall
  { structCallFun = fun
  , structCallArgs = map unStructInfo sis
  , structCallDecArgs = map unStructInfo . filter isDecreasing $ sis
  }

-- This is where we  check a function call. We go through  the list of arguments
-- and find the  indices of those which are decreasing.  Note that this approach
-- is only guaranteed to  work when the arguments to the  function are named, so
-- e.g.
-- foo (x:xs) (y:ys) = foo xs (y:ys)
-- won't necessarily work, but
-- foo (x:xs) yys@(y:ys) = foo xs yys
-- will.
toStructCall :: SrcCall -> StructCall
toStructCall srcCall = mkStructCall (srcCallFun srcCall) $ toStructArgs 0 (srcCallArgs srcCall)
  where
    toStructArgs _ [] = []
    toStructArgs index ((param, toVar -> Just v):args)
      | v `isParam` param = Unchanged index : toStructArgs (index + 1) args
      | v `isParamSubterm` param = Decreasing index : toStructArgs (index + 1) args
    toStructArgs index (_:args) = toStructArgs (index + 1) args

-- Check if there is some way to lexicographically order the arguments so that
-- they are structurally decreasing. Essentially, in order for there to be, we
-- must be able to find some argument which is always either unchanged or
-- decreasing. We can then remove every call where that argument is decreasing
-- and recurse.
structDecreasing :: Var -> [StructCall] -> Result ()
structDecreasing _ [] = mempty
structDecreasing funName calls
  | null sharedArgs = addError funName "Non-structural recursion" mempty
  | otherwise = structDecreasing funName $ (map removeSharedArgs . filter noneDecreasing) calls
  where
    sharedArgs = foldl1 L.intersect (structCallArgs <$> calls)
    noneDecreasing call = null $ structCallDecArgs call `L.intersect` sharedArgs
    removeSharedArgs call = call { structCallArgs = structCallArgs call L.\\ sharedArgs }
