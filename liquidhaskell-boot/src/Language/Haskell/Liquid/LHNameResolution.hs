-- | This module provides a GHC 'Plugin' that allows LiquidHaskell to be hooked directly into GHC's
-- compilation pipeline, facilitating its usage and adoption.

{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE LambdaCase                 #-}

module Language.Haskell.Liquid.LHNameResolution
  ( collectTypeAliases
  , resolveLHNames
  , exprArg
  ) where

import           Liquid.GHC.API         as GHC hiding (Expr, panic)
import qualified  Language.Haskell.Liquid.GHC.Misc        as LH
import           Language.Haskell.Liquid.Types.Names
import           Language.Haskell.Liquid.Types.RType

import           Control.Monad.Writer
import           Data.Data (Data, gmapT)
import           Data.Generics (extT)


import qualified Data.HashSet                            as HS
import qualified Data.HashMap.Strict                     as HM

import           Language.Fixpoint.Types hiding (Error, panic)
import           Language.Haskell.Liquid.Types.Errors (TError(ErrDupNames, ErrResolve), panic)
import           Language.Haskell.Liquid.Types.Specs
import           Language.Haskell.Liquid.Types.Types

import qualified Text.PrettyPrint.HughesPJ as PJ
import qualified Text.Printf               as Printf

-- | Collects type aliases from the current module and its dependencies.
--
-- It doesn't matter at the moment in which module a type alias is defined.
-- Type alias names cannot be qualified at the moment, and therefore their
-- names identify them uniquely.
collectTypeAliases
  :: Module
  -> BareSpec
  -> [(StableModule, LiftedSpec)]
  -> HM.HashMap Symbol (GHC.Module, RTAlias Symbol BareType)
collectTypeAliases m bs deps =
    let spec = getBareSpec bs
        bsAliases = [ (rtName a, (m, a)) | a <- map val (aliases spec) ]
        depAliases =
          [ (rtName a, (unStableModule sm, a))
          | (sm, lspec) <- deps
          , a <- map val (HS.toList $ liftedAliases lspec)
          ]
     in
        HM.fromList $ bsAliases ++ depAliases

-- | Converts occurrences of LHNUnresolved to LHNResolved using the provided
-- type aliases and GlobalRdrEnv.
resolveLHNames
  :: HM.HashMap Symbol (Module, RTAlias Symbol BareType)
  -> GlobalRdrEnv
  -> BareSpec
  -> Either [Error] BareSpec
resolveLHNames taliases globalRdrEnv =
    (\(bs, es) -> if null es then Right bs else Left es) .
    runWriter .
    mapMLocLHNames (\l -> (<$ l) <$> resolveLHName l) .
    fixExpressionArgsOfTypeAliases taliases
  where
    resolveLHName lname = case val lname of
      LHNUnresolved LHTcName s
        | isTuple s ->
          pure $ LHNResolved (LHRGHC $ GHC.tupleTyConName GHC.BoxedTuple (tupleArity s)) s
        | isList s ->
          pure $ LHNResolved (LHRGHC GHC.listTyConName) s
        | s == "*" ->
          pure $ LHNResolved (LHRGHC GHC.liftedTypeKindTyConName) s
        | otherwise ->
          case HM.lookup s taliases of
            Just (m, _) -> pure $ LHNResolved (LHRLogic $ LogicName s m) s
            Nothing -> case GHC.lookupGRE globalRdrEnv (mkLookupGRE LHTcName s) of
              [e] -> pure $ LHNResolved (LHRGHC $ GHC.greName e) s
              es@(_:_) -> do
                tell [ErrDupNames
                        (LH.fSrcSpan lname)
                        (pprint s)
                        (map (PJ.text . showPprUnsafe) es)
                     ]
                pure $ val lname
              [] -> do
                tell [errResolve "type constructor" "Cannot resolve name" (s <$ lname)]
                pure $ val lname
      LHNUnresolved LHDataConName s ->
          case GHC.lookupGRE globalRdrEnv (mkLookupGRE LHDataConName s) of
            [e] ->
              pure $ LHNResolved (LHRGHC $ GHC.greName e) s
            es@(_:_) -> do
              tell [ErrDupNames
                      (LH.fSrcSpan lname)
                      (pprint s)
                      (map (PJ.text . showPprUnsafe) es)
                   ]
              pure $ val lname
            [] -> do
              tell [errResolve "data constructor" "Cannot resolve name" (s <$ lname)]
              pure $ val lname
      n@(LHNResolved (LHRLocal _) _) -> pure n
      n ->
        let sp = Just $ LH.sourcePosSrcSpan $ loc lname
         in panic sp $ "resolveLHNames: Unexpected resolved name: " ++ show n

    errResolve :: PJ.Doc -> String -> LocSymbol -> Error
    errResolve k msg lx = ErrResolve (LH.fSrcSpan lx) k (pprint (val lx)) (PJ.text msg)

    mkLookupGRE ns s =
      let m = LH.takeModuleNames s
          n = LH.dropModuleNames s
          nString = symbolString n
          -- TODO: Maybe change the parser so dataConNameP doesn't include the
          -- parentheses around infix operators.
          maybeUnpar = case nString of
            '(':rest -> init rest
            _ -> nString
          oname = GHC.mkOccName (mkGHCNameSpace ns) maybeUnpar
          rdrn =
            if m == "" then
              GHC.mkRdrUnqual oname
            else
              GHC.mkRdrQual (GHC.mkModuleName $ symbolString m) oname
       in GHC.LookupRdrName rdrn GHC.SameNameSpace

    mkGHCNameSpace = \case
      LHTcName -> GHC.tcName
      LHDataConName -> GHC.dataName

    tupleArity s =
      let a = read $ drop 5 $ symbolString s
       in if a > 64 then
            error $ "tupleArity: Too large (more than 64): " ++ show a
          else
            a

-- | Changes unresolved names to local resolved names in the body of type
-- aliases.
resolveBoundVarsInTypeAliases :: BareSpec -> BareSpec
resolveBoundVarsInTypeAliases = updateAliases resolveBoundVars
  where
    resolveBoundVars boundVars = \case
      LHNUnresolved LHTcName s ->
        if elem s boundVars then
          LHNResolved (LHRLocal s) s
        else
          LHNUnresolved LHTcName s
      n ->
        error $ "resolveLHNames: Unexpected resolved name: " ++ show n

    -- Applies a function to the body of type aliases, passes to every call the
    -- arguments of the alias.
    updateAliases f bs =
      let spec = getBareSpec bs
       in MkBareSpec spec
            { aliases = [ Loc sp0 sp1 (a { rtBody = mapLHNames (f args) (rtBody a) })
                        | Loc sp0 sp1 a <- aliases spec
                        , let args = rtTArgs a ++ rtVArgs a
                        ]
            }

-- | The expression arguments of type aliases are initially parsed as
-- types. This function converts them to expressions.
--
-- For instance, in @Prop (Ev (plus n n))@ where `Prop` is the alias
--
-- > {-@ type Prop E = {v:_ | prop v = E} @-}
--
-- the parser builds a type for @Ev (plus n n)@.
--
fixExpressionArgsOfTypeAliases
  :: HM.HashMap Symbol (Module, RTAlias Symbol BareType)
  -> BareSpec
  -> BareSpec
fixExpressionArgsOfTypeAliases taliases =
    mapBareTypes go . resolveBoundVarsInTypeAliases
  where
    go :: BareType -> BareType
    go (RApp c@(BTyCon { btc_tc = Loc _ _ (LHNUnresolved LHTcName s) }) ts rs r)
      | Just (_, rta) <- HM.lookup s taliases =
        RApp c (fixExprArgs (btc_tc c) rta (map go ts)) (map goRef rs) r
    go (RApp c ts rs r) =
        RApp c (map go ts) (map goRef rs) r
    go (RAppTy t1 t2 r)  = RAppTy (go t1) (go t2) r
    go (RFun  x i t1 t2 r) = RFun  x i (go t1) (go t2) r
    go (RAllT a t r)     = RAllT a (go t) r
    go (RAllP a t)       = RAllP a (go t)
    go (RAllE x t1 t2)   = RAllE x (go t1) (go t2)
    go (REx x t1 t2)     = REx   x (go t1) (go t2)
    go (RRTy e r o t)    = RRTy  e r o     (go t)
    go t@RHole{}         = t
    go t@RVar{}          = t
    go t@RExprArg{}      = t
    goRef (RProp ss t)   = RProp ss (go t)

    fixExprArgs lname rta ts =
      let n = length (rtTArgs rta)
          (targs, eargs) = splitAt n ts
          msg = "FIX-EXPRESSION-ARG: " ++ showpp (rtName rta)
          toExprArg = exprArg (LH.fSourcePos lname) msg
       in targs ++ [ RExprArg $ toExprArg e <$ lname | e <- eargs ]

mapBareTypes :: (BareType -> BareType) -> BareSpec -> BareSpec
mapBareTypes f  = go
  where
    go :: Data a => a -> a
    go = gmapT (go `extT` f)

-- | exprArg converts a tyVar to an exprVar because parser cannot tell
--   this function allows us to treating (parsed) "types" as "value"
--   arguments, e.g. type Matrix a Row Col = List (List a Row) Col
--   Note that during parsing, we don't necessarily know whether a
--   string is a type or a value expression. E.g. in tests/pos/T1189.hs,
--   the string `Prop (Ev (plus n n))` where `Prop` is the alias:
--     {-@ type Prop E = {v:_ | prop v = E} @-}
--   the parser will chomp in `Ev (plus n n)` as a `BareType` and so
--   `exprArg` converts that `BareType` into an `Expr`.
exprArg :: SourcePos -> String -> BareType -> Expr
exprArg l msg = notracepp ("exprArg: " ++ msg) . go
  where
    go :: BareType -> Expr
    go (RExprArg e)     = val e
    go (RVar x _)       = EVar (symbol x)
    go (RApp x [] [] _) = EVar (getLHNameSymbol $ val $ btc_tc x)
    go (RApp f ts [] _) = mkEApp (getLHNameSymbol <$> btc_tc f) (go <$> ts)
    go (RAppTy t1 t2 _) = EApp (go t1) (go t2)
    go z                = panic sp $ Printf.printf "Unexpected expression parameter: %s in %s" (show z) msg
    sp                  = Just (LH.sourcePosSrcSpan l)
