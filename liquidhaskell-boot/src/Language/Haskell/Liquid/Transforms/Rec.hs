{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}

module Language.Haskell.Liquid.Transforms.Rec (
     transformRecExpr, isIdTRecBound, setIdTRecBound
     ) where

import           Control.Arrow                        (second)
import           Control.Monad.State
import qualified Data.HashMap.Strict                  as M
import           Data.Hashable
import           Data.Maybe (mapMaybe)
import           Data.Word (Word64)
import           Liquid.GHC.API      as Ghc hiding (panic)
import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.GHC.Play
import           Language.Haskell.Liquid.Misc         (mapSndM)
import           Language.Fixpoint.Misc               (mapSnd) -- , traceShow)
import           Language.Haskell.Liquid.Types.Errors
import           Prelude                              hiding (error)

import qualified Data.List                            as L


transformRecExpr :: CoreProgram -> CoreProgram
transformRecExpr cbs = pg
  -- TODO-REBARE weird GHC crash on Data/Text/Array.hs | isEmptyBag $ filterBag isTypeError e
  -- TODO-REBARE weird GHC crash on Data/Text/Array.hs = pg
  -- TODO-REBARE weird GHC crash on Data/Text/Array.hs | otherwise
  -- TODO-REBARE weird GHC crash on Data/Text/Array.hs = panic Nothing ("Type-check" ++ showSDoc (pprMessageBag e))
  where
    pg     = inlineFailCases pg0
    pg0    = evalState (transPg (inlineLoopBreaker <$> cbs)) initEnv
    -- (_, e) = lintCoreBindings [] pg


-- | Changes top level bindings of the form
--
-- > v = \x1...xn ->
-- >   letrec v0 = \y0...ym -> e0
-- >       in v0 xj..xn
--
-- to
--
-- > v = \x1...xj y0...ym ->
-- >   e0 [ v0 := v x1...xj y0...ym ]
--
inlineLoopBreaker :: Bind Id -> Bind Id
inlineLoopBreaker (NonRec x e)
    | Just (lbx, lbe, lbargs) <- hasLoopBreaker be =
       let lbe' = sub (M.singleton lbx e') lbe
        in Rec [(x, foldr Lam lbe' (αs ++ take (length as - length lbargs) as))]
  where
    (αs, as, be) = collectTyAndValBinders e

    e' = L.foldl' App (L.foldl' App (Var x) (Type . TyVarTy <$> αs)) (Var <$> as)

    hasLoopBreaker :: CoreExpr -> Maybe (Var, CoreExpr, [CoreExpr])
    hasLoopBreaker (Let (Rec [(x1, e1)]) e2)
      | (Var x2, args) <- collectArgs e2
      , isLoopBreaker x1
      , x1 == x2
      , all isVar args
      , L.isSuffixOf (mapMaybe getVar args) as
      = Just (x1, e1, args)
    hasLoopBreaker _                               = Nothing

    isLoopBreaker =  isStrongLoopBreaker . occInfo . idInfo

    getVar (Var x) = Just x
    getVar _ = Nothing

    isVar (Var x) = True
    isVar _ = False

inlineLoopBreaker bs
  = bs

-- | Inlines bindings of the form
--
-- > let v = \x -> e0
-- >  in e1
--
-- whenever all of the following hold:
--  * "fail" is a prefix of variable @v@,
--  * @x@ is not free in @e0@, and
--  * v is applied to some value in @e1@.
--
-- In addition to inlining, this function also beta reduces
-- the resulting expressions @(\x -> e0) a@ by replacing them
-- with @e0@.
--
inlineFailCases :: CoreProgram -> CoreProgram
inlineFailCases = (go [] <$>)
  where
    go su (Rec xes)    = Rec (mapSnd (go' su) <$> xes)
    go su (NonRec x e) = NonRec x (go' su e)

    go' su (App (Var x) _)       | isFailId x, Just e <- getFailExpr x su = e
    go' su (Let (NonRec x ex) e) | isFailId x   = go' (addFailExpr x (go' su ex) su) e

    go' su (App e1 e2)      = App (go' su e1) (go' su e2)
    go' su (Lam x e)        = Lam x (go' su e)
    go' su (Let xs e)       = Let (go su xs) (go' su e)
    go' su (Case e x t alt) = Case (go' su e) x t (goalt su <$> alt)
    go' su (Cast e c)       = Cast (go' su e) c
    go' su (Tick t e)       = Tick t (go' su e)
    go' _  e                = e

    goalt su (Alt c xs e)   = Alt c xs (go' su e)

    isFailId x  = isLocalId x && isSystemName (varName x) && L.isPrefixOf "fail" (show x)
    getFailExpr = L.lookup

    addFailExpr x (Lam v e) su
      | not (elemVarSet v $ exprFreeVars e)  = (x, e):su
    addFailExpr _ _         _  = impossible Nothing "internal error" -- this cannot happen


type TE = State TrEnv

data TrEnv = Tr { freshIndex  :: !Word64
                , _loc        :: SrcSpan
                }

initEnv :: TrEnv
initEnv = Tr 0 noSrcSpan

transPg :: Traversable t
        => t (Bind CoreBndr)
        -> State TrEnv (t (Bind CoreBndr))
transPg = mapM transBd

transBd :: Bind CoreBndr
        -> State TrEnv (Bind CoreBndr)
transBd (NonRec x e) = fmap (NonRec x) (transExpr =<< mapBdM transBd e)
transBd (Rec xes)    = Rec <$> mapM (mapSndM (mapBdM transBd)) xes

transExpr :: CoreExpr -> TE CoreExpr
transExpr e
  | isNonPolyRec e' && not (null tvs)
  = trans tvs ids bs e'
  | otherwise
  = return e
  where (tvs, ids, e'')       = collectTyAndValBinders e
        (bs, e')              = collectNonRecLets e''

isNonPolyRec :: Expr CoreBndr -> Bool
isNonPolyRec (Let (Rec xes) _) = any nonPoly (snd <$> xes)
isNonPolyRec _                 = False

nonPoly :: CoreExpr -> Bool
nonPoly = null . fst . splitForAllTyCoVars . exprType

collectNonRecLets :: Expr t -> ([Bind t], Expr t)
collectNonRecLets = go []
  where go bs (Let b@(NonRec _ _) e') = go (b:bs) e'
        go bs e'                      = (reverse bs, e')

appTysAndIds :: [Var] -> [Id] -> Id -> Expr b
appTysAndIds tvs ids x = mkApps (mkTyApps (Var x) (map TyVarTy tvs)) (map Var ids)

trans :: Foldable t
      => [TyVar]
      -> [Var]
      -> t (Bind Id)
      -> Expr Var
      -> State TrEnv (Expr Id)
trans vs ids bs (Let (Rec xes) expr)
  = fmap (mkLam . mkLet') (makeTrans vs liveIds e')
  where liveIds = mkAlive <$> ids
        mkLet' e = foldr Let e bs
        mkLam e = foldr Lam e $ vs ++ liveIds
        e'      = Let (Rec xes') expr
        xes'    = second mkLet' <$> xes

trans _ _ _ _ = panic Nothing "TransformRec.trans called with invalid input"

makeTrans :: [TyVar]
          -> [Var]
          -> Expr Var
          -> State TrEnv (Expr Var)
makeTrans vs ids (Let (Rec xes) e)
 = do fids    <- mapM (mkFreshIds vs ids) xs
      let (ids', ys) = unzip fids
      let yes  = appTysAndIds vs ids <$> ys
      ys'     <- mapM fresh xs
      let su   = M.fromList $ zip xs (Var <$> ys')
      let rs   = zip ys' yes
      let es'  = zipWith (mkE ys) ids' es
      let xes' = zip ys es'
      return   $ mkRecBinds rs (Rec xes') (sub su e)
 where
   (xs, es)       = unzip xes
   mkSu ys ids'   = mkSubs ids vs ids' (zip xs ys)
   mkE ys ids' e' = mkCoreLams (vs ++ ids') (sub (mkSu ys ids') e')

makeTrans _ _ _ = panic Nothing "TransformRec.makeTrans called with invalid input"

mkRecBinds :: [(b, Expr b)] -> Bind b -> Expr b -> Expr b
mkRecBinds xes rs expr = Let rs (L.foldl' f expr xes)
  where f e (x, xe) = Let (NonRec x xe) e

mkSubs :: (Eq k, Hashable k)
       => [k] -> [Var] -> [Id] -> [(k, Id)] -> M.HashMap k (Expr b)
mkSubs ids tvs xs ys = M.fromList $ s1 ++ s2
  where s1 = second (appTysAndIds tvs xs) <$> ys
        s2 = zip ids (Var <$> xs)

mkFreshIds :: [TyVar]
           -> [Var]
           -> Var
           -> State TrEnv ([Var], Id)
mkFreshIds tvs origIds var
  = do ids'  <- mapM fresh origIds
       let ids'' = map setIdTRecBound ids'
       let t  = mkForAllTys ((`Bndr` Required) <$> tvs) $ mkType (reverse ids'') $ varType var
       let x' = setVarType var t
       return (ids'', x')
  where
    mkType ids ty = foldl (\t x -> FunTy FTF_T_T ManyTy (varType x) t) ty ids -- FIXME(adinapoli): Is 'VisArg' OK here?

-- NOTE [Don't choose transform-rec binders as decreasing params]
-- --------------------------------------------------------------
--
-- We don't want to select a binder created by TransformRec as the
-- decreasing parameter, since the user didn't write it. Furthermore,
-- consider T1065. There we have an inner loop that decreases on the
-- sole list parameter. But TransformRec prepends the parameters to the
-- outer `groupByFB` to the inner `groupByFBCore`, and now the first
-- decreasing parameter is the constant `xs0`. Disaster!
--
-- So we need a way to signal to L.H.L.Constraint.Generate that we
-- should ignore these copied Vars. The easiest way to do that is to set
-- a flag on the Var that we know won't be set, and it just so happens
-- GHC has a bunch of optional flags that can be set by various Core
-- analyses that we don't run...
setIdTRecBound :: Id -> Id
-- This is an ugly hack..
setIdTRecBound = modifyIdInfo (`setCafInfo` NoCafRefs)

isIdTRecBound :: Id -> Bool
isIdTRecBound = not . mayHaveCafRefs . cafInfo . idInfo

class Freshable a where
  fresh :: a -> TE a

instance Freshable Word64 where
  fresh _ = freshWord64

instance Freshable Unique where
  fresh _ = freshUnique

instance Freshable Var where
  fresh v = fmap (setVarUnique v) freshUnique

freshWord64 :: MonadState TrEnv m => m Word64
freshWord64
  = do s <- get
       let n = freshIndex s
       put s{freshIndex = n+1}
       return n

freshUnique :: MonadState TrEnv m => m Unique
freshUnique = fmap (mkUnique 'X') freshWord64

-- Do not apply transformations to inner code

mapBdM :: Monad m => t -> a -> m a
mapBdM _ = return
