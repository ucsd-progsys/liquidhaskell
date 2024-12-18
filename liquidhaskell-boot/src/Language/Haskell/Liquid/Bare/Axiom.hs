{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}

{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

-- | This module contains the code that DOES reflection; i.e. converts Haskell
--   definitions into refinements.

module Language.Haskell.Liquid.Bare.Axiom ( makeHaskellAxioms, strengthenSpecWithMeasure, makeAssumeReflectAxioms, AxiomType(..) ) where

import Prelude hiding (error)
import Prelude hiding (mapM)
import qualified Control.Exception         as Ex

-- import           Control.Monad.Except      hiding (forM, mapM)
-- import           Control.Monad.State       hiding (forM, mapM)
import qualified Text.PrettyPrint.HughesPJ as PJ -- (text)
import qualified Data.HashSet              as S
import qualified Data.Maybe                as Mb
import Control.Monad.Trans.State.Lazy (runState, get, put)

import qualified Language.Haskell.Liquid.Measure as Ms
import qualified Language.Fixpoint.Types as F
import qualified Liquid.GHC.API as Ghc
import qualified Language.Haskell.Liquid.GHC.Misc as GM
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Transforms.CoreToLogic
import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.Names
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.RTypeOp
import           Language.Haskell.Liquid.Types.Specs
import           Language.Haskell.Liquid.Types.Types

import           Language.Haskell.Liquid.Bare.Resolve as Bare
import           Language.Haskell.Liquid.Bare.Types   as Bare
import           Language.Haskell.Liquid.Bare.Measure as Bare
import           Language.Haskell.Liquid.UX.Config
import qualified Data.List as L
import Control.Applicative
import Control.Arrow (second)
import Data.Function (on)
import qualified Data.Map as Map
import qualified Data.HashMap.Strict as M

findDuplicatePair :: Ord k => (a -> k) -> [a] -> Maybe (a, a)
findDuplicatePair key xs =
  Mb.listToMaybe
    [ (a, b)
    | a:b:_ <- L.groupBy ((==) `on` key) (L.sortOn key xs)
    ]

findDuplicateBetweenLists :: (Ord k) => (a -> k) -> [a] -> [a] -> Maybe (a, a)
findDuplicateBetweenLists key l1 l2 =
  findDuplicate key (Map.fromList [ (key x, x) | x <- l1 ]) l2
  where
    findDuplicate :: Ord k => (a -> k) -> Map.Map k a -> [a] -> Maybe (a, a)
    findDuplicate key' seen l2' =
      Mb.listToMaybe
      [ (x, y) | x <- l2', Just y <- [Map.lookup (key' x) seen]]

-----------------------------------------------------------------------------------------------
makeHaskellAxioms :: GhcSrc -> Bare.Env -> Bare.TycEnv -> LogicMap -> GhcSpecSig -> Ms.BareSpec
                  -> Bare.Lookup [(Ghc.Var, LocSpecType, F.Equation)]
-----------------------------------------------------------------------------------------------
makeHaskellAxioms src env tycEnv lmap spSig spec = do
  let refDefs = getReflectDefs src spSig spec env
  return (makeAxiom env tycEnv lmap <$> refDefs)

-----------------------------------------------------------------------------------------------
--          Returns a list of elements, one per assume reflect                               --
-- Each element is made of:                                                                  --
-- * The variable name of the actual function                                                --
-- * The refined type of actual function, where the post-condition is strengthened with      --
--   ``VV == pretendedFn arg1 arg2 ...`                                                      --
-- * The assume reflect equation, linking the pretended and actual function:                 --
--   `actualFn arg1 arg 2 ... = pretendedFn arg1 arg2 ...`                                   --
makeAssumeReflectAxioms :: GhcSrc -> Bare.Env -> Bare.TycEnv -> GhcSpecSig -> Ms.BareSpec
                  -> Bare.Lookup [(Ghc.Var, LocSpecType, F.Equation)]
-----------------------------------------------------------------------------------------------
makeAssumeReflectAxioms src env tycEnv spSig spec = do
  -- Send an error message if we're redefining a reflection
  case findDuplicatePair val reflActSymbols <|> findDuplicateBetweenLists val refSymbols reflActSymbols of
    Just (x , y) -> Ex.throw $ mkError y $
                      "Duplicate reflection of " ++
                      show (lhNameToUnqualifiedSymbol <$> x) ++
                      " and " ++
                      show (lhNameToUnqualifiedSymbol <$> y)
    Nothing -> return $ turnIntoAxiom <$> Ms.asmReflectSigs spec
  where
    turnIntoAxiom (actual, pretended) = makeAssumeReflectAxiom spSig env embs (actual, pretended)
    refDefs                 = getReflectDefs src spSig spec env
    embs                    = Bare.tcEmbs       tycEnv
    refSymbols              =
      (\(x, _, v, _) -> F.atLoc x $ makeGHCLHName (Ghc.getName v) (F.symbol v)) <$> refDefs
    reflActSymbols          = fst <$> Ms.asmReflectSigs spec

-----------------------------------------------------------------------------------------------
-- Processes one `assume reflect` and returns its axiom element, as detailed in              --
-- `makeAssumeReflectAxioms`. Can also be used to compute the updated SpecType of            --
-- a type where we add the post-condition that actual and pretended are the same             --
makeAssumeReflectAxiom :: GhcSpecSig -> Bare.Env -> F.TCEmb Ghc.TyCon
                       -> (Located LHName, Located LHName) -- actual function and pretended function
                       -> (Ghc.Var, LocSpecType, F.Equation)
-----------------------------------------------------------------------------------------------
makeAssumeReflectAxiom sig env tce (actual, pretended) =
   -- The actual and pretended function must have the same type
  if pretendedTy == actualTy then
    (actualV, actual{val = aty at}, actualEq)
  else
    Ex.throw $ mkError actual $
      show qPretended ++ " and " ++ show qActual ++ " should have the same type. But " ++
      "types " ++ F.showpp pretendedTy ++ " and " ++ F.showpp actualTy  ++ " do not match."
  where
    at = val $ strengthenSpecWithMeasure sig env actualV pretended{val=qPretended}

    -- Get the Ghc.Var's of the actual and pretended function names
    actualV = case Bare.lookupGhcIdLHName env actual of
      Right x -> x
      Left _ -> panic (Just $ GM.fSrcSpan actual) "function to reflect not in scope"
    pretendedV = case Bare.lookupGhcIdLHName env pretended of
      Right x -> x
      Left _ -> panic (Just $ GM.fSrcSpan pretended) "function to reflect not in scope"
    -- Get the qualified name symbols for the actual and pretended functions
    lhNameToSymbol lx =
      F.symbol $
      Mb.fromMaybe (panic (Just $ GM.fSrcSpan lx) $ "expected a resolved Haskell name: " ++ show lx) $
      getLHGHCName $
      val lx
    qActual = lhNameToSymbol actual
    qPretended = lhNameToSymbol pretended
    -- Get the GHC type of the actual and pretended functions
    actualTy = Ghc.varType actualV
    pretendedTy = Ghc.varType pretendedV

    -- The return type of the function
    out   = rTypeSort tce $ ares at
    -- The arguments names and types, as given by `AxiomType`
    xArgs = fmap (rTypeSort tce) <$> aargs at

    -- Expression of the equation. It is just saying that the actual and pretended functions are the same
    -- when applied to the same arguments
    le    = foldl F.EApp (F.EVar qPretended) (F.EVar . fst <$> xArgs)

    actualEq = F.mkEquation qActual xArgs le out

strengthenSpecWithMeasure :: GhcSpecSig -> Bare.Env
                       -> Ghc.Var -- var owning the spec
                       -> LocSymbol     -- measure name
                       -> Located AxiomType
-----------------------------------------------------------------------------------------------
strengthenSpecWithMeasure sig env actualV qPretended =
    qPretended{ val = addSingletonApp allowTC (val qPretended) rt}
  where
    -- Get the GHC type of the actual and pretended functions
    actualTy = Ghc.varType actualV

    -- Compute the refined type of the actual function. See `makeAssumeType` for details
    sigs                    = gsTySigs sig ++ gsAsmSigs sig -- We also look into assumed signatures
    -- Try to get the specification of the actual function from the signatures
    mbT   = val <$> lookup actualV sigs
    -- Refines that spec. If the specification is not in the scope, just use the GHC type as a dummy spec
    -- to proceed with.
    rt    = fromRTypeRep .
            (\trep@RTypeRep{..} ->
                trep{ty_info = fmap (\i -> i{permitTC = Just allowTC}) ty_info}) .
            toRTypeRep $ Mb.fromMaybe (ofType actualTy) mbT
    allowTC = typeclass (getConfig env)

-- Gets the definitions of all the symbols that `BareSpec` wants to reflect.
--
-- Because we allow to name private variables here, not all symbols can easily
-- be turned into `Ghc.Var`. Essentially, `findVarDefType` can initially only
-- fetch the definitions of public variables. We use a fixpoint so that for each
-- newly retrieved definition, we get the list of variables used inside it and
-- record them in a HashMap so that in the next round, we might be able to get
-- more definitions (because once you have a variable, it's easy to get its
-- unfolding).
--
-- Iterates until no new definition is found. In which case, we fail
-- if there are still symbols left which we failed to find the source for.
getReflectDefs :: GhcSrc -> GhcSpecSig -> Ms.BareSpec -> Bare.Env
               -> [(LocSymbol, Maybe SpecType, Ghc.Var, Ghc.CoreExpr)]
getReflectDefs src sig spec env =
  searchInTransitiveClosure symsToResolve initialDefinedMap []
  where
    sigs                    = gsTySigs sig
    symsToResolve =
      map Left (S.toList (Ms.reflects spec)) ++
      map Right (S.toList (Ms.privateReflects spec))
    cbs = Ghc.flattenBinds $ _giCbs src
    initialDefinedMap          = M.empty

    -- First argument of the `searchInTransitiveClosure` function should always
    -- decrease.
    -- The second argument contains the Vars that appear free in the definitions
    -- of the symbols in the third argument.
    -- The third argument contains the symbols that have been resolved.
    --
    -- The set of symbols in the union of the first and third argument should
    -- remain constant in every recursive call. Moreover, both arguments are
    -- disjoint.
    --
    -- Base case: No symbols left to resolve - we're good
    searchInTransitiveClosure [] _ acc = acc
    -- Recursive case: there are some left.
    searchInTransitiveClosure toResolve fvMap acc = if null found
         then case newToResolve of
                -- No one newly found but no one left to process - we're good
                [] -> acc
                -- No one newly found but at least one symbol left - we throw
                -- an error
                x:_ -> Ex.throw . either mkError mkError x $
                  "Not found in scope nor in the amongst these variables: " ++
                    foldr (\x1 acc1 -> acc1 ++ " , " ++ show x1) "" newFvMap
         else searchInTransitiveClosure newToResolve newFvMap newAcc
      where
        -- Try to get the definitions of the symbols that are left (`toResolve`)
        resolvedSyms = findVarDefType cbs sigs env fvMap <$> toResolve
        -- Collect the newly found definitions
        found     = Mb.catMaybes resolvedSyms
        -- Add them to the accumulator
        newAcc    = acc ++ found
        -- Add any variable occurrence in them to `fvMap`
        newFvMap = foldl addFreeVarsToMap fvMap found
        -- Collect all the symbols that still failed to be resolved in this
        -- iteration
        newToResolve = [x | (x, Nothing) <- zip toResolve resolvedSyms]

    -- Collects the free variables in an expression and inserts them to the
    -- provided map between symbols and variables. Especially useful to collect
    -- private variables, since it's the only way to reach them (seeing them in
    -- other unfoldings)
    addFreeVarsToMap fvMap (_, _, _, expr) =
      let freeVarsSet = getAllFreeVars expr
          newVars =
            M.fromList [(Bare.varLocSym var, var) | var <- freeVarsSet]
      in M.union fvMap newVars

    getAllFreeVars = Ghc.exprSomeFreeVarsList (const True)

-- | Names for functions that need to be reflected
--
-- > Left nameInScope | Right qualifiedPrivateName
type ToReflectName = Either (Located LHName) LocSymbol

-- Finds the definition of a variable in the given Core binds, or in the
-- unfoldings of a Var. Used for reflection. Returns the same
-- `LHName` given as argument, the SpecType of this symbol, its corresponding
-- variable and definition (the `CoreExpr`).
--
-- Takes as arguments:
-- - The list of bindings, usually taken from the GhcSrc
-- - A map of signatures, used to retrieve the `SpecType`
-- - The current environment, that can be used to resolve symbols
-- - An extra map between symbols and variables for those symbols that are hard
--   to resolve, especially if they are private symbols from foreign
--   dependencies. This map will be used as a fallback if the default resolving
--   mechanism fails.
--
-- Returns `Nothing` iff the symbol could not be resolved. No error is thrown in
-- this case since this function is used by the fixpoint mechanism of
-- `getReflectDefs`. Which will collect all the symbols that could (not) yet be
-- resolved.
--
-- Errors can be raised whenever the symbol was found but the rest of the
-- process failed (no unfoldings available, lifted functions not exported,
-- etc.).
findVarDefType :: [(Ghc.Id, Ghc.CoreExpr)] -> [(Ghc.Var, LocSpecType)] -> Bare.Env
               -> M.HashMap LocSymbol Ghc.Var -> ToReflectName
               -> Maybe (LocSymbol, Maybe SpecType, Ghc.Var, Ghc.CoreExpr)
findVarDefType cbs sigs env _defs (Left x) =
  case L.find ((val x ==) . makeGHCLHNameFromId . fst) cbs of
  -- YL: probably ok even without checking typeclass flag since user cannot
  -- manually reflect internal names
  Just (v, e) ->
    Just (fmap getLHNameSymbol x, val <$> lookup v sigs, v, e)
  Nothing     -> do
    let ecall = panic (Just $ GM.fSrcSpan x) "function to reflect not found"
        var = either ecall id (Bare.lookupGhcIdLHName env x)
        info = Ghc.idInfo var
        unfolding = getExprFromUnfolding . Ghc.realUnfoldingInfo $ info
    case unfolding of
      Just e ->
        Just (fmap getLHNameSymbol x, val <$> lookup var sigs, var, e)
      _ ->
        Ex.throw $ mkError x $ unwords
          [ "Symbol exists but is not defined in the current file,"
          , "and no unfolding is available in the interface files"
          ]

findVarDefType _cbs sigs _env defs (Right x) = do
    var <- M.lookup x defs
    let info = Ghc.idInfo var
    let unfolding = getExprFromUnfolding . Ghc.realUnfoldingInfo $ info
    case unfolding of
      Just e ->
        Just (x, val <$> lookup var sigs, var, e)
      _ ->
        Ex.throw $ mkError x $ unwords
          [ "Symbol exists but is not defined in the current file,"
          , "and no unfolding is available in the interface files"
          ]

getExprFromUnfolding :: Ghc.Unfolding -> Maybe Ghc.CoreExpr
getExprFromUnfolding (Ghc.CoreUnfolding expr _ _ _ _) = Just expr
getExprFromUnfolding _ = Nothing

--------------------------------------------------------------------------------
makeAxiom :: Bare.Env -> Bare.TycEnv -> LogicMap
          -> (LocSymbol, Maybe SpecType, Ghc.Var, Ghc.CoreExpr)
          -> (Ghc.Var, LocSpecType, F.Equation)
--------------------------------------------------------------------------------
makeAxiom env tycEnv lmap (x, mbT, v, def)
            = (v, t, e)
  where
    (t, e)  = makeAssumeType allowTC embs lmap dm x mbT v def
    embs    = Bare.tcEmbs       tycEnv
    dm      = Bare.tcDataConMap tycEnv
    allowTC = typeclass (getConfig env)

mkError :: PPrint a => Located a -> String -> Error
mkError x str = ErrHMeas (sourcePosSrcSpan $ loc x) (pprint $ val x) (PJ.text str)

-- This function is uded to generate the fixpoint code for reflected functions
makeAssumeType
  :: Bool -- ^ typeclass enabled
  -> F.TCEmb Ghc.TyCon -> LogicMap -> DataConMap -> LocSymbol -> Maybe SpecType
  -> Ghc.Var -> Ghc.CoreExpr
  -> (LocSpecType, F.Equation)
makeAssumeType allowTC tce lmap dm sym mbT v def
  = ( sym {val = aty at `strengthenRes` F.subst su ref}
    , F.mkEquation 
        symbolV 
        (fmap (second $ F.sortSubst sortSub) xts)
        (F.sortSubstInExpr sortSub (F.subst su le))
        (F.sortSubst sortSub out)
    )
  where
    symbolV = F.symbol v
    rt    = fromRTypeRep .
            (\trep@RTypeRep{..} ->
                trep{ty_info = fmap (\i -> i{permitTC = Just allowTC}) ty_info}) .
            toRTypeRep $ Mb.fromMaybe (ofType τ) mbT
    τ     = Ghc.varType v
    at    = addSingletonApp allowTC symbolV rt
    out   = rTypeSort tce $ ares at
    xArgs = F.EVar . fst <$> aargs at
    _msg  = unwords [showpp sym, showpp mbT]
    le    = case runToLogicWithBoolBinds bbs tce lmap dm mkErr (coreToLogic allowTC def') of
              Right e -> e
              Left  e -> panic Nothing (show e)
    ref        = F.Reft (F.vv_, F.PAtom F.Eq (F.EVar F.vv_) le)
    mkErr s    = ErrHMeas (sourcePosSrcSpan $ loc sym) (pprint $ val sym) (PJ.text s)
    bbs        = filter isBoolBind xs

    -- rTypeSortExp produces monomorphic sorts from polymorphic types.
    -- As an example, for 
    -- id :: a -> a ... id x = x 
    -- we got: 
    -- define id (x : a#foobar) : a#foobar = { (x : a#foobar) }
    -- Using FObj instead of a real type variable (FVar i) This code solves the
    -- issue by creating a sort substitution that replaces those "fake" type variables
    -- with actual ones.
    -- define id (x : @-1) : a@-1 = { (x : a@-1) }
    (tyVars, _) = Ghc.splitForAllTyCoVars τ
    sortSub     = F.mkSortSubst $ zip (fmap F.symbol tyVars) (F.FVar <$> freeSort)
    -- We need sorts that aren't polluted by rank-n types, we can't just look at
    -- the term to determine statically what is the "maximum" sort bound ex:
    -- freeSort = [1 + (maximum $ -1 : F.sortAbs out : fmap (F.sortAbs . snd) xts) ..] 
    -- as some variable may be bound to something of rank-n type.  In
    -- SortCheck.hs in fixpoint they just start at 42 for some reason.  I think
    -- Negative Debruijn indices (levels :^)) are safer
    freeSort    = [-1, -2 ..]

    (xs, def') = GM.notracePpr "grabBody" $ grabBody allowTC (Ghc.expandTypeSynonyms τ) $ normalize allowTC def
    su         = F.mkSubst  $ zip (F.symbol     <$> xs) xArgs
                           ++ zip (simplesymbol <$> xs) xArgs
    xts        = [(F.symbol x, rTypeSortExp tce t) | (x, t) <- aargs at]

rTypeSortExp :: F.TCEmb Ghc.TyCon -> SpecType -> F.Sort
rTypeSortExp tce = typeSort tce . Ghc.expandTypeSynonyms . toType False

grabBody :: Bool -- ^ typeclass enabled
         -> Ghc.Type -> Ghc.CoreExpr -> ([Ghc.Var], Ghc.CoreExpr)
grabBody allowTC (Ghc.ForAllTy _ ty) e
  = grabBody allowTC ty e
grabBody allowTC@False Ghc.FunTy{ Ghc.ft_arg = tx, Ghc.ft_res = t} e | Ghc.isClassPred tx
  = grabBody allowTC t e
grabBody allowTC@True Ghc.FunTy{ Ghc.ft_arg = tx, Ghc.ft_res = t} e | isEmbeddedDictType tx
  = grabBody allowTC t e
grabBody allowTC torig@Ghc.FunTy {} (Ghc.Let (Ghc.NonRec x e) body)
  = grabBody allowTC torig (subst (x,e) body)
grabBody allowTC Ghc.FunTy{ Ghc.ft_res = t} (Ghc.Lam x e)
  = (x:xs, e') where (xs, e') = grabBody allowTC t e
grabBody allowTC t (Ghc.Tick _ e)
  = grabBody allowTC t e
grabBody allowTC ty@Ghc.FunTy{} e
  = (txs++xs, e')
   where (ts,tr)  = splitFun ty
         (xs, e') = grabBody allowTC tr (foldl Ghc.App e (Ghc.Var <$> txs))
         txs      = [ stringVar ("ls" ++ show i) t |  (t,i) <- zip ts [(1::Int)..]]
grabBody _ _ e
  = ([], e)

splitFun :: Ghc.Type -> ([Ghc.Type], Ghc.Type)
splitFun = go []
  where go acc Ghc.FunTy{ Ghc.ft_arg = tx, Ghc.ft_res = t} = go (tx:acc) t
        go acc t                                           = (reverse acc, t)


isBoolBind :: Ghc.Var -> Bool
isBoolBind v = isBool (ty_res $ toRTypeRep ((ofType $ Ghc.varType v) :: RRType ()))

strengthenRes :: SpecType -> F.Reft -> SpecType
strengthenRes st rf = go st
  where
    go (RAllT a t r)   = RAllT a (go t) r
    go (RAllP p t)     = RAllP p $ go t
    go (RFun x i tx t r) = RFun x i tx (go t) r
    go t               =  t `strengthen` ofReft rf

class Subable a where
  subst :: (Ghc.Var, Ghc.CoreExpr) -> a -> a

instance Subable Ghc.Var where
  subst (x, ex) z
    | x == z, Ghc.Var y <- ex = y
    | otherwise           = z

instance Subable Ghc.CoreExpr where
  subst (x, ex) (Ghc.Var y)
    | x == y    = ex
    | otherwise = Ghc.Var y
  subst su (Ghc.App f e)
    = Ghc.App (subst su f) (subst su e)
  subst su (Ghc.Lam x e)
    = Ghc.Lam x (subst su e)
  subst su (Ghc.Case e x t alts)
    = Ghc.Case (subst su e) x t (subst su <$> alts)
  subst su (Ghc.Let (Ghc.Rec xes) e)
    = Ghc.Let (Ghc.Rec (fmap (subst su) <$> xes)) (subst su e)
  subst su (Ghc.Let (Ghc.NonRec x ex) e)
    = Ghc.Let (Ghc.NonRec x (subst su ex)) (subst su e)
  subst su (Ghc.Cast e t)
    = Ghc.Cast (subst su e) t
  subst su (Ghc.Tick t e)
    = Ghc.Tick t (subst su e)
  subst _ e
    = e

instance Subable Ghc.CoreAlt where
  subst su (Ghc.Alt c xs e) = Ghc.Alt c xs (subst su e)

data AxiomType = AT { aty :: SpecType, aargs :: [(F.Symbol, SpecType)], ares :: SpecType }
  deriving Show

-- | Specification for Haskell function
--
-- @addSingletonApp allowTC f (x:_ -> y: -> {v:_ | p}@ produces a type
-- @x:_ -> y:_ -> {v:_ | p && v = f x y}@
--
addSingletonApp :: Bool -> F.Symbol -> SpecType -> AxiomType
addSingletonApp allowTC s st = AT to (reverse xts) res
  where
    (to, (_,xts, Just res)) = runState (go st) (1,[], Nothing)
    go (RAllT a t r) = RAllT a <$> go t <*> return r
    go (RAllP p t) = RAllP p <$> go t
    go (RFun x i tx t r) | isErasable tx = (\t' -> RFun x i tx t' r) <$> go t
    go (RFun x ii tx t r) = do
      (i,bs,mres) <- get
      let x' = unDummy x i
      put (i+1, (x', tx):bs,mres)
      t' <- go t
      return $ RFun x' ii tx t' r
    go t = do
      (i,bs,_) <- get
      let ys = reverse $ map fst bs
      let t' = strengthen t (singletonApp s ys)
      put (i, bs, Just t')
      return t'
    isErasable = if allowTC then isEmbeddedClass else isClassType
unDummy :: F.Symbol -> Int -> F.Symbol
unDummy x i
  | x /= F.dummySymbol = x
  | otherwise          = F.symbol ("lq" ++ show i)

singletonApp :: F.Symbolic a => F.Symbol -> [a] -> UReft F.Reft
singletonApp s ys = MkUReft r mempty
  where
    r             = F.exprReft (F.eApps (F.EVar s) (F.eVar <$> ys))
