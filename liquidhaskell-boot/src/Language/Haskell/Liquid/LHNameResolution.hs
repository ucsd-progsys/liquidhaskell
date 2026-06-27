-- | This module provides functions to resolve names in specs.
--
-- There are two major namespaces in LH:
--
-- 1) The names of Haskell entities
-- 2) The names of logic entities
--
-- At the moment LH resolves names to Haskell entities, while resolving logic
-- entities remains work in progress.
--
-- Haskell entities include all functions that LH might reflect, or types that
-- might be referred in refinement types, type aliases or other annotations.
--
-- Logic entities include the names of reflected functions, inlined functions,
-- uninterpreted functions, predefined functions, local bindings, reflected data
-- constructors and parameters of Haskell functions in specs of other local
-- bindings.
--
-- The resolution pipeline goes as follows.
--
-- * First the module specs are parsed into a 'BareSpecParsed'.
--   Here all names are unresolved.
-- * Next the names of Haskell entities are resolved by 'resolveLHNames'.
--   For now, this pass doesn't change the type of the names.
-- * Next the names of logic entities are resolved. This pass produces
--   a 'BareSpecLHName', where 'Symbol's are replaced with 'LHName'.
--
-- * A bit of name resolution is done in 'makeSpecVars' in "Language.Haskell.Liquid.Bare"
--   to check if the names in @ignore@ annotations refer to functions or type
--   class methods.
--
-- 'BareSpecLHName' has an approximate bijection to 'BareSpec' via a 'LogicNameEnv'
-- which allows to convert 'LHName' to an unambiguous form of 'Symbol'
-- and back. The bijection is implemented with the functions 'toBareSpecLHName'
-- and 'fromBareSpecLHName'. This allows to use liquid-fixpoint functions
-- unmodified as they will continue to operate on (now unambiguous) Symbols.
-- The bijection is approximate because in the roundtrip the representation of
-- LHName's might change.
--
-- At the same time, the 'BareSpecLHName' form is kept to serialize and to
-- resolve names of modules that import the specs.
--

{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeApplications           #-}

module Language.Haskell.Liquid.LHNameResolution
  ( resolveLHNames
  , resolveSymbolToTcName
  , exprArg
  , fromBareSpecLHName
  , toBareSpecLHName
  , symbolToLHName
  , LogicNameEnv(..)
  ) where

import qualified Liquid.GHC.API         as GHC hiding (Expr, panic)
import qualified Language.Haskell.Liquid.GHC.Interface   as LH
import qualified Language.Haskell.Liquid.GHC.Misc        as LH
import           Language.Haskell.Liquid.Types.Names
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.RTypeOp

import           Control.Monad.Except (ExceptT, runExceptT, throwError)
import           Control.Monad ((<=<), mplus, unless, void)
import           Control.Monad.Identity
import           Control.Monad.State.Strict
import           Data.Bifunctor (first, second)
import qualified Data.Char                               as Char
import           Data.Coerce (coerce)
import           Data.Data (Data, gmapM)
import           Data.Generics (extM)


import qualified Data.HashSet                            as HS
import qualified Data.HashMap.Strict                     as HM
import           Data.List (find, isSuffixOf, nubBy, partition)
import           Data.List.Extra (dropEnd)
import qualified Data.Map as Map
import           Data.Maybe (mapMaybe, maybeToList)
import qualified Data.Text                               as Text
import qualified GHC.Types.Name.Occurrence

import           Language.Fixpoint.Types as F hiding (Error, panic)
import qualified Language.Haskell.Liquid.Bare.Resolve as Resolve
import           Language.Haskell.Liquid.Bare.Types (LocalVars(lvNames), LocalVarDetails(lvdLclEnv))
import           Language.Fixpoint.Misc as Misc
import           Language.Haskell.Liquid.Name.LogicNameEnv
import qualified Language.Haskell.Liquid.Types.DataDecl as DataDecl
import           Language.Haskell.Liquid.Types.Errors (TError(ErrDupNames, ErrResolve), panic)
import           Language.Haskell.Liquid.Types.Specs as Specs
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.UX.Config
import           Language.Haskell.Liquid.WiredIn

import qualified Text.PrettyPrint.HughesPJ as PJ
import qualified Text.Printf               as Printf

-- | Collects type aliases from the current module and its dependencies.
--
-- By construction, type alises from transitive dependencies are neglected (see 'moduleAliases').
-- We do so because all type aliases in scope are added to the 'LiftedSpec' later.
-- Aliases with the same unqualified name coexist during name resolution,
-- as long as we have a means to disambiguate (namely, by qualifing the import).
-- In this case, when building the 'LiftedSpec' we carry only the first such alias according
-- to lexicographic order.
collectTypeAliases
  :: GHC.ImportedMods
  -> GHC.Module
  -> BareSpecParsed
  -> TargetDependencies
  -> InScopeEnv (RTAlias Symbol ())
collectTypeAliases impMods thisModule spec deps =
    let bsAliases = mkAliasEnv thisModule impMods (thisModule, bsNames)
        bsNames = [ (val . rtName $ rta, void rta) | rta <- aliases spec]
        depAliases = map (mkAliasEnv thisModule impMods) $
          [ (m, depNames)
          | (sm, lspec) <- HM.toList (getDependencies deps)
          , let m = GHC.unStableModule sm
          , let depNames = [ (val . rtName $ rta , void rta)
                           | rta <- HS.toList $ liftedAliases lspec
                           ]
          ]
     in
        unionAliasEnvs $ bsAliases : depAliases

--------------------------------------------------------------------------------
-- | [NOTE:EXPRESSION-ALIASES]:
--
-- In a lifted spec, expression aliases include fully unfolded predicate,
-- inline, and define annotations. By contrast, a bare spec’s expression
-- aliases include only predicate aliases. This is because symbols from these
-- three kinds of annotations are unfolded uniformly in logical expressions
-- during spec lifting.
--
-- Inlines and defines are converted to expression aliases via 'lmapEalias',
-- which assigns them a 'GeneratedLogicName'. This allows us to distinguish
-- them from predicate aliases, which should be the only 'LogicName's among
-- expression aliases.
--
-- Here, we collect the symbols of inlines and defines from expression aliases
-- to identify their uses when resolving logic variable names.
-- This should be redundant when these aliases are resolved via the
-- logic environments and a dedicated lifted field for inlines is added.
--------------------------------------------------------------------------------
collectInlinesAndDefines:: TargetDependencies -> HS.HashSet Symbol
collectInlinesAndDefines deps = HS.unions
  [ HS.map lhNameToResolvedSymbol depInlinesAndDefines
  | (_, lspec) <- HM.toList (getDependencies deps)
  , let exprAliases = HS.map (val . rtName) $ liftedEaliases lspec
        depInlinesAndDefines = HS.filter (not . isResolvedLogicName) exprAliases
   ]

-- | Converts occurrences of LHNUnresolved to LHNResolved using the provided
-- type aliases and GlobalRdrEnv.
resolveLHNames
  :: Config
  -> GHC.Module
  -> LocalVars
  -> GHC.ImportedMods
  -> GHC.GlobalRdrEnv
  -> BareSpecParsed
  -> TargetDependencies
  -> Either [Error] (BareSpec, LogicNameEnv, LogicMap)
resolveLHNames cfg thisModule localVars impMods globalRdrEnv bareSpec0 dependencies =
  flip evalState RenameOutput { roErrors = [], roUsedNames = [], roUsedDataCons = mempty } $
    runExceptT $ do
      -- Prepare type aliases for resolution.
      sp0 <- lift $ fixExpressionArgsOfTypeAliases taliases $ resolveBoundVarsInTypeAliases bareSpec0

      checkErrors

      -- Pre-resolve the head names of data and newtype declarations to
      -- GHC TyCons, bypassing type alias lookup.  This ensures that a
      -- user-defined data type is not confused with an imported type alias
      -- of the same name (e.g. 'TT' in GHC.Types_LHAssumptions).  When
      -- the same name is used in a type position (as opposed to the head
      -- of a data declaration) the type alias continues to take priority
      -- via the normal 'resolveLHName' path below.
      let sp0' = sp0
                   { dataDecls  = map resolveDataDeclHeadName (dataDecls  sp0)
                   , newtyDecls = map resolveDataDeclHeadName (newtyDecls sp0)
                   }

      -- First resolution pass: A generic traversal that resolves names
      -- of Haskell entities and type alias binders.
      sp1 <- lift $ mapMLocLHNames (\l -> (<$ l) <$> resolveLHName l) sp0'

      -- Data decls contain fieldnames that introduce measures with the
      -- same names. We resolve them before constructing the logic
      -- environments.
      dataDecls <- lift $ mapM (mapDataDeclFieldNamesM resolveFieldLogicName) (dataDecls sp1)
      let sp2 = sp1 {dataDecls}

      checkErrors

      -- Second resolution pass: a traversal to resolve logic names using the following
      -- lookup environments.
      let (inScopeEnv, logicNameEnv0, privateReflectNames) =
            makeLogicEnvs impMods thisModule sp2 dependencies

          -- Add resolved local defines to the logic map.
          lmap1 = lmap <> mkLogicMap (HM.fromList $
                   [ (F.val $ lhNameToResolvedSymbol <$> k,
                      (val <$> v) { lmVar = lhNameToResolvedSymbol <$> k })
                   | (k,v) <- defines sp2 ])
      sp3 <- lift $ fromBareSpecLHName <$>
                  resolveLogicNames
                    cfg
                    thisModule
                    inScopeEnv
                    globalRdrEnv
                    lmap1
                    localVars
                    logicNameEnv0
                    privateReflectNames
                    depsInlinesAndDefines
                    sp2

      checkErrors

      -- Rebuild the logic map with fully-resolved define bodies from sp3.
      -- lmap1 was built before resolveLogicNames, so body symbols (e.g. "len")
      -- are bare/unresolved.  sp3 has gone through logic name resolution and
      -- fromBareSpecLHName, so its defines carry properly qualified symbols.
      let lmap2 = lmap <> mkLogicMap (HM.fromList
                   [ (F.val $ lhNameToResolvedSymbol <$> k,
                      v { lmVar = lhNameToResolvedSymbol <$> k })
                   | (k, v) <- defines sp3 ])

      dcs <- gets roUsedDataCons
      return (sp3 { usedDataCons = dcs }, logicNameEnv0, lmap2)
  where
    -- Early exit name resolution if errors are found and pass them to the output.
    checkErrors :: ExceptT [Error] (StateT RenameOutput Identity) ()
    checkErrors = do
      es <- gets roErrors
      unless (null es) (throwError es)

    -- We collect type aliases before resolving names so we have a means to disambiguate
    -- imported and local ones (according to their resolution status).
    taliases = collectTypeAliases impMods thisModule bareSpec0 dependencies
    depsInlinesAndDefines = collectInlinesAndDefines dependencies

    -- Add defines from dependencies to the logical map.
    lmap =
        (LH.listLMap <>) $
        mconcat $
        map (mkLogicMap . HM.map (fmap lhNameToResolvedSymbol) . liftedDefines) $
        HM.elems $
        getDependencies dependencies

    resolveFieldLogicName n =
      case n of
        LHNUnresolved LHLogicNameBinder s -> pure $ makeLogicLHName s thisModule Nothing
        _ -> panic Nothing $ "unexpected name: " ++ show n

    -- | Pre-resolve the head name of a data/newtype declaration to a GHC
    -- TyCon, bypassing type alias resolution.  This prevents an imported
    -- type alias (e.g. @type TT = {v:Bool|v}@ in GHC.Types_LHAssumptions)
    -- from shadowing a user-defined data type with the same name.
    -- 'mapMLocLHNames' leaves already-resolved names untouched, so any name
    -- resolved here will not be visited again in the first resolution pass.
    resolveDataDeclHeadName decl =
        decl { DataDecl.tycName = resolveDataName (DataDecl.tycName decl) }
      where
        resolveDataName (DataDecl.DnName lname) =
            DataDecl.DnName (resolveHeadLHName lname)
        resolveDataName dn = dn

        resolveHeadLHName lname = case val lname of
          LHNUnresolved (LHTcName lcl) s ->
            case GHC.lookupGRE globalRdrEnv (mkLookupGRE (LHTcName lcl) s) of
              [e] -> LHNResolved (LHRGHC (GHC.greName e)) s <$ lname
              _   -> lname  -- leave unresolved; normal pass will handle it
          _ -> lname  -- already resolved or not a TyCon name

    resolveLHName lname =
      case val lname of
        LHNUnresolved (LHTcName lcl) s
          | isTuple s ->
            pure $ LHNResolved (LHRGHC $ GHC.tupleTyConName GHC.BoxedTuple (tupleArity s)) s
          | isList s ->
            pure $ LHNResolved (LHRGHC GHC.listTyConName) s
          | s == "*" ->
            pure $ LHNResolved (LHRGHC GHC.liftedTypeKindTyConName) s
          | otherwise ->
            case resolveTypeAlias taliases s of
              -- Priority is given to aliases defined in the current module,
              -- so name occurrences are resolved using them, disregarding
              -- any imported aliases with the same name.
              -- This allows the user to shadow imported aliases.
              FoundTypeAliases { tarLocallyDefined = [(m, _, _)] } ->
                pure $ makeLogicLHName (LH.dropModuleNames s) m Nothing
              FoundTypeAliases { tarImported = [(_, lh, _)]
                               , tarLocallyDefined = []} | lcl == LHAnyModuleNameF ->
                pure lh
              -- If multiple matches are found, report the ambiguous name and return it.
              tar@(FoundTypeAliases { }) -> do addError $ errResolveTypeAlias (s <$ lname) tar
                                               pure $ val lname
              NoSuchTypeAlias alts -> lookupGRELHName alts (LHTcName lcl) lname s
        LHNUnresolved ns@(LHVarName lcl) s
          | isDataCon s ->
              lookupGRELHName [] (LHDataConName lcl) lname s
          | not (LH.isQualifiedSym s)
          , Just v <- Resolve.lookupLetBoundVar localVars (atLoc lname s)
          ->
              pure $ LHNResolved (LHRGHC (GHC.getName v)) s
          | otherwise ->
              lookupGRELHName [] ns lname s
        LHNUnresolved LHLogicNameBinder s ->
          pure $ makeLogicLHName s thisModule Nothing
        n@(LHNUnresolved LHLogicName _) ->
          -- This one will be resolved by resolveLogicNames
          pure n
        LHNUnresolved ns@(LHDataConName _) s -> lookupGRELHName [] ns lname s
        n@LHNResolved { } -> pure n

    lookupGRELHName alts ns lname s =
      case maybeDropImported ns $ GHC.lookupGRE globalRdrEnv (mkLookupGRE ns s) of
        [e] -> do
          let n = GHC.greName e
          pure $ LHNResolved (LHRGHC n) s
        es@(_:_) -> do
          addError
            (ErrDupNames
               (LH.fSrcSpan lname)
               (nameSpaceKind ns)
               (pprint s)
               (map (PJ.text . GHC.showPprUnsafe) es)
            )
          pure $ val lname
        [] -> do
          addError
            (errResolve alts (nameSpaceKind ns) "Cannot resolve name" (s <$ lname))
          pure $ val lname

    maybeDropImported ns es
      | localNameSpace ns = filter GHC.isLocalGRE es
      | otherwise = es

    localNameSpace = \case
      LHDataConName lcl -> lcl == LHThisModuleNameF
      LHVarName lcl -> lcl == LHThisModuleNameF
      LHTcName lcl -> lcl == LHThisModuleNameF
      LHLogicNameBinder -> False
      LHLogicName -> False

    nameSpaceKind :: LHNameSpace -> PJ.Doc
    nameSpaceKind = \case
      LHTcName LHAnyModuleNameF -> "type constructor"
      LHTcName LHThisModuleNameF -> "locally-defined type constructor"
      LHDataConName LHAnyModuleNameF -> "data constructor"
      LHDataConName LHThisModuleNameF -> "locally-defined data constructor"
      LHVarName LHAnyModuleNameF -> "variable"
      LHVarName LHThisModuleNameF -> "variable from the current module"
      LHLogicNameBinder -> "logic name binder"
      LHLogicName -> "logic name"

    isDataCon s = case Text.uncons (Text.takeWhileEnd (/= '.') (symbolText s)) of
      Just (c, _) -> Char.isUpper c || c == ':'
      Nothing -> False

tupleArity :: Symbol -> Int
tupleArity s =
      let a = read $ drop 5 $ symbolString s
       in if a > 64 then
            error $ "tupleArity: Too large (more than 64): " ++ show a
          else
            a

errResolve :: [Symbol] -> PJ.Doc -> String -> LocSymbol -> Error
errResolve alts k msg ls =
  ErrResolve
    (LH.fSrcSpan ls)
    k
    (pprint $ val ls)
    (if null alts then
        PJ.text msg
      else
        PJ.text msg PJ.$$
        PJ.sep (PJ.text "Maybe you meant one of:" : map pprint alts)
    )


-- | Produces an LHName from a symbol by looking it in the rdr environment.
resolveSymbolToTcName :: GHC.GlobalRdrEnv -> LocSymbol -> Either Error (Located LHName)
resolveSymbolToTcName globalRdrEnv lx
    | isTuple s =
      pure $ LHNResolved (LHRGHC $ GHC.tupleTyConName GHC.BoxedTuple (tupleArity s)) s <$ lx
    | isList s =
      pure $ LHNResolved (LHRGHC GHC.listTyConName) s <$ lx
    | s == "*" =
      pure $ LHNResolved (LHRGHC GHC.liftedTypeKindTyConName) s <$ lx
    | otherwise =
      case GHC.lookupGRE globalRdrEnv (mkLookupGRE (LHTcName LHAnyModuleNameF) s) of
        [e] -> Right $ LHNResolved (LHRGHC $ GHC.greName e) s <$ lx
        [] -> Left $ errResolve [] "type constructor" "Cannot resolve name" lx
        es -> Left $ ErrDupNames
                (LH.fSrcSpan lx)
                "type constructor"
                (pprint s)
                (map (PJ.text . GHC.showPprUnsafe) es)
  where
    s = val lx

-- | Resolving logic names can produce errors and new names to add to the
-- environment. New names might be produced when encountering data constructors
-- or functions from the logic map.
data RenameOutput = RenameOutput
    { roErrors :: [Error]
      -- | Names of used data constructors, and names of used reflected
      -- functions and used logic map names
    , roUsedNames :: [LHName]
      -- | Names of used data constructors
    , roUsedDataCons :: HS.HashSet LHName
    }

addError :: Error -> State RenameOutput ()
addError e = modify (\ro -> ro { roErrors = e : roErrors ro })

addName :: LHName -> State RenameOutput ()
addName n = modify (\ro -> ro { roUsedNames = n : roUsedNames ro })

addDataConsName :: LHName -> State RenameOutput ()
addDataConsName n = modify (\ro -> ro { roUsedDataCons = HS.insert n (roUsedDataCons ro) })

mkLookupGRE :: LHNameSpace -> Symbol -> GHC.LookupGRE GHC.GREInfo
mkLookupGRE ns s =
    let m = LH.takeModuleNames s
        n = LH.dropModuleNames s
        nString = symbolString n
        oname = GHC.mkOccName (mkGHCNameSpace ns) nString
        rdrn =
          if m == "" then
            GHC.mkRdrUnqual oname
          else
            GHC.mkRdrQual (GHC.mkModuleName $ symbolString m) oname
     in GHC.LookupRdrName rdrn (mkWhichGREs ns)
  where
    mkWhichGREs :: LHNameSpace -> GHC.WhichGREs GHC.GREInfo
    mkWhichGREs = \case
      LHTcName _ -> GHC.SameNameSpace
      LHDataConName _ -> GHC.SameNameSpace
      LHVarName _ -> GHC.RelevantGREs
        { GHC.includeFieldSelectors = GHC.WantNormal
        , GHC.lookupVariablesForFields = True
        , GHC.lookupTyConsAsWell = False
        }
      LHLogicNameBinder -> panic Nothing "mkWhichGREs: unexpected namespace LHLogicNameBinder"
      LHLogicName -> panic Nothing "mkWhichGREs: unexpected namespace LHLogicName"

    mkGHCNameSpace = \case
      LHTcName _ -> GHC.tcName
      LHDataConName _ -> GHC.dataName
      LHVarName _ -> GHC.Types.Name.Occurrence.varName
      LHLogicNameBinder -> panic Nothing "mkGHCNameSpace: unexpected namespace LHLogicNameBinder"
      LHLogicName -> panic Nothing "mkGHCNameSpace: unexpected namespace LHLogicName"

-- | Changes unresolved names to local resolved names in the body of type
-- aliases.
resolveBoundVarsInTypeAliases :: BareSpecParsed -> BareSpecParsed
resolveBoundVarsInTypeAliases = updateAliases resolveBoundVars
  where
    resolveBoundVars boundVars = \case
      LHNUnresolved (LHTcName lcl) s ->
        if elem s boundVars then
          LHNResolved (LHRLocal s) s
        else
          LHNUnresolved (LHTcName lcl) s
      n ->
        error $ "resolveLHNames: Unexpected resolved name: " ++ show n

    -- Applies a function to the body of type aliases, passes to every call the
    -- arguments of the alias.
    updateAliases f spec =
       spec
            { aliases = [ a { rtBody = mapLHNames (f args) (rtBody a) }
                        | a <- aliases spec
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
-- | @fixExpressionArgsOfTypeAliases taliases spec@ converts types to
-- values when they appear in value positions of type aliases according
-- to @taliases@.
--
-- The expression arguments of type aliases are initially parsed as
-- types. This function converts them to expressions.
--
-- For instance, in @Prop (Ev (plus n n))@ where `Prop` is the alias
--
-- > {-@ type Prop E = {v:_ | prop v = E} @-}
--
-- the parser builds a type for @Ev (plus n n)@, making a type
-- constructor of @Ev@ and type variables of @plus@ and @n@. But
-- @Ev@ is really a data constructor, @plus@ is a function, and @n@
-- is a value.
fixExpressionArgsOfTypeAliases
  :: InScopeEnv (RTAlias Symbol ())
  -> BareSpecParsed
  -> StateT RenameOutput Identity BareSpecParsed
fixExpressionArgsOfTypeAliases taliases = mapMBareTypes go
  where
    go :: BareTypeParsed -> StateT RenameOutput Identity BareTypeParsed
    go (RApp c@(BTyCon { btc_tc = lname@(Loc _ _ (LHNUnresolved (LHTcName _) s)) }) ts rs r)
      | tar@(FoundTypeAliases imported local) <- resolveTypeAlias taliases s =
          case (imported, local) of
               -- Local alias definitions get priority over imported ones.
               -- This allows the user to shadow imported aliases.
               (_ ,[(_, _, rta)]) ->
                 RApp <$> pure c <*> fixExprArgs (btc_tc c) rta (mapM go ts) <*> mapM goRef rs <*> pure r
               ([(_, _, rta)] , []) ->
                 RApp <$> pure c <*> fixExprArgs (btc_tc c) rta (mapM go ts) <*> mapM goRef rs <*> pure r
               -- Report ambiguos name and continue traversing.
               _ -> do
                 addError $ errResolveTypeAlias (s <$ lname) tar
                 RApp <$> pure c <*> mapM go ts <*> mapM goRef rs <*> pure r
    go (RApp c ts rs r)    = RApp <$> pure c <*> mapM go ts <*> mapM goRef rs <*> pure r
    go (RAppTy t1 t2 r)    = RAppTy <$> go t1 <*> go t2 <*> pure r
    go (RFun  x i t1 t2 r) = RFun <$> pure x <*> pure i <*> go t1 <*> go t2 <*> pure r
    go (RAllT a t r)       = RAllT <$> pure a <*> go t <*> pure r
    go (RAllP a t)         = RAllP a <$> go t
    go (REx x t1 t2)       = REx  x <$> go t1 <*> go t2
    go (RRTy e r o t)      = RRTy  e r o  <$> go t
    go t@RHole{}           = pure t
    go t@RVar{}            = pure t
    go t@RExprArg{}        = pure t
    goRef (RProp ss t)     = RProp ss <$> go t

    fixExprArgs lname rta mts = do
      ts <- mts
      let n = length (rtTArgs rta)
          (targs, eargs) = splitAt n ts
          msg = "FIX-EXPRESSION-ARG: " ++ showpp (rtName rta)
          toExprArg = exprArg (LH.fSourcePos lname) msg
      pure $ targs ++ [ RExprArg $ toExprArg e <$ lname | e <- eargs ]

mapMBareTypes :: forall m a.(Data a, Monad m) => (BareTypeParsed -> m BareTypeParsed) -> a -> m a
mapMBareTypes f  = go
  where
    go :: forall b. Data b => b -> m b
    go = gmapM (go `extM` f)

-- | exprArg converts a tyVar to an exprVar because parser cannot tell
--   this function allows us to treating (parsed) "types" as "value"
--   arguments, e.g. type Matrix a Row Col = List (List a Row) Col
--   Note that during parsing, we don't necessarily know whether a
--   string is a type or a value expression. E.g. in tests/pos/T1189.hs,
--   the string `Prop (Ev (plus n n))` where `Prop` is the alias:
--     {-@ type Prop E = {v:_ | prop v = E} @-}
--   the parser will chomp in `Ev (plus n n)` as a `BareType` and so
-- | @exprArg@ converts a type to a value.
--
--   At parse time the arguments of type aliases are all treated as types.
--   This needs fixing before verification because some arguments are
--   meant to be values. Hence, this function to correct the
--   arguments in question. See the documentation of
--   @fixExpressionArgsOfTypeAliases@ for some more context.
exprArg :: SourcePos -> String -> BareTypeParsed -> ExprV LocSymbol
exprArg l msg = notracepp ("exprArg: " ++ msg) . go
  where
    go :: BareTypeParsed -> ExprV LocSymbol
    go (RExprArg e)     = val e
    go (RVar (BTV x) _) = EVar x
    go (RApp x [] [] _) = EVar (getLHNameSymbol <$> btc_tc x)
    go (RApp f ts [] _) = eApps (EVar (renameAmbiguousCtor . getLHNameSymbol <$> btc_tc f)) (go <$> ts)
    go (RAppTy t1 t2 _) = EApp (go t1) (go t2)
    go z                = panic sp $ Printf.printf "Unexpected expression parameter: %s in %s" (showpp $ parsedToBareType z) msg
    sp                  = Just (LH.sourcePosSrcSpan l)

renameAmbiguousCtor :: Symbol -> Symbol
renameAmbiguousCtor x
  | Just n <- isTyTupleSizedSymbol x = tmTupleSizedSymbol n
  | otherwise = x

-- | A type alias 'lookupInScopeEnv' that distinguishes locally defined names
-- from imported ones based on their resolution status:
-- unresolved names correspond to type aliases defined in the current module,
-- whereas all imported names are expected to be resolved.
resolveTypeAlias
   :: InScopeEnv (RTAlias Symbol a)
   -> Symbol
   -> TypeAliasResolution (RTAlias Symbol a)
resolveTypeAlias taliases s = case lookupInScopeEnv taliases  s of
  Right ns -> let (imported, local) =
                    partition (\(_,lhname,_) -> isResolvedLogicName lhname ) ns
              in FoundTypeAliases imported local
  Left alts -> NoSuchTypeAlias alts

-- | When resolving type aliases we either find matching 'LHName's
-- or similar, but distinct, 'Symbol's.
data TypeAliasResolution a
  = NoSuchTypeAlias [Symbol]
  | FoundTypeAliases
      { tarImported :: [(GHC.Module, LHName, a)]
      , tarLocallyDefined :: [(GHC.Module, LHName, a)]
      }

errResolveTypeAlias :: LocSymbol -> TypeAliasResolution (RTAlias x a) -> Error
errResolveTypeAlias ls (FoundTypeAliases imported local) =
  ErrDupNames (LH.fSrcSpan ls) "type alias" (pprint $ val ls)
    (
      -- Currently, multiple local definitions prevent this error from being raised,
      -- because duplicate names are discarded when constructing the alias environment
      -- for each individual module,
      -- and a local alias always shadows any imported one. Such duplicates are detected
      -- later during validation of the final target spec.
      --
      -- Also, note that collected local type alias names remain unresolved at this stage,
      -- so we must extract their symbol using a function that can safely handle unresolved
      -- names.
      map (\(_, lhn, rta) -> pprint (getLHNameSymbol lhn)
                             PJ.<+>
                             PJ.text "defined in current module at"
                             PJ.<+>
                             pprint  (LH.fSrcSpan . rtName $ rta)
          )
          local
     ++
     map (\(m, lhn, rta) -> pprint (lhNameToUnqualifiedSymbol lhn)
                            PJ.<+>
                            PJ.text "imported from module"
                            PJ.<+>
                            PJ.text (GHC.moduleNameString (GHC.moduleName m))
                            PJ.<+>
                            PJ.text "defined at"
                            PJ.<+>
                            pprint (LH.fSrcSpan . rtName $ rta)
         )
         imported
    )
errResolveTypeAlias ls (NoSuchTypeAlias alts) =
  errResolve alts "type alias" "Cannot resolve name" ls


-- | An environment of names in scope
--
-- We construct it using 'mkAliasEnv' and 'unionAliasEnvs' in such a way that each
-- symbol in the environment corresponds to all matching 'LHNames' along with
-- the aliases of the module we import it from.
-- Currently, the parameter is used to include the type alias representation when
-- we 'collectTypeAliases'.
type InScopeEnv a = SEnv [(GHC.ModuleName, (GHC.Module, LHName, a))]

type InScopeNonReflectedEnv = InScopeEnv ()

-- | Looks for the 'LHName's in scope with the given symbol,
-- taking possible qualification prefixes into account.
-- Returns a list of close but different symbols or a non-empty list
-- with the matched names.
lookupInScopeEnv
  :: InScopeEnv a -> Symbol -> Either [Symbol] [(GHC.Module, LHName, a)]
lookupInScopeEnv env s = do
    -- The symbol might be qualified or not,
    -- but we use the unqualified symbol for the lookup.
    let n = LH.dropModuleNames s
    case lookupSEnvWithDistance n env of
      Alts closeSyms -> Left closeSyms
      F.Found xs -> do
         let q = LH.takeModuleNames s
         case filter ((GHC.mkFastString (symbolString q) ==) . GHC.moduleNameFS . fst) xs of
           [] -> Left $ map (maybeQualifySymbol n . symbol . GHC.moduleNameString . fst) xs
           ys -> Right $ map snd ys
  where
    maybeQualifySymbol n m =
      if m == "" then n else LH.qualifySymbol m n

-- | Builds an environment of non-reflected names in scope from the module
-- imports for the current module, the spec of the current module, and the specs
-- of the dependencies.
--
-- Also returns a LogicNameEnv constructed from the same names.
-- Also returns the names of reflected private functions.
-- Also returns the set of all names that aren't handled yet by name resolution.
makeLogicEnvs
  :: GHC.ImportedMods
  -> GHC.Module
  -> BareSpecParsed
  -> TargetDependencies
  -> ( InScopeNonReflectedEnv
     , LogicNameEnv
     , HS.HashSet LocSymbol
     )
makeLogicEnvs impMods thisModule spec dependencies =
    let depsLogicNames =
          map (fmap collectLiftedSpecLogicNames) dependencyPairs
        logicNames =
          (thisModule, thisModuleNames) : depsLogicNames
        nonReflectedNamesWithUnit =
          map
            (second $ map (, ()) . filter isNonReflectedLogicName)
            logicNames
        thisModuleNames = concat
          [ [ reflectLHName thisModule (val n)
            | n <- concat
              [ map fst (asmReflectSigs spec)
              , HS.toList (reflects spec)
              , HS.toList (opaqueReflects spec)
              , HS.toList (inlines spec)
              , HS.toList (hmeas spec)
              , map fst (sigs spec)
              ]
            ]
          , [ val (msName m) | m <- measures spec ]
          , [ val (msName m) | m <- cmeasures spec ]
          , map fst $
             concatMap DataDecl.dcFields $ concat $
             mapMaybe DataDecl.tycDCons $
             dataDecls spec
          , [ val (rtName ea) | ea <- ealiases spec ]
          ]
        privateReflectNames =
          mconcat $
            privateReflects spec : map (liftedPrivateReflects . snd) dependencyPairs
     in
        ( unionAliasEnvs $ map (mkAliasEnv thisModule impMods) nonReflectedNamesWithUnit
        , mkLogicNameEnv (concatMap snd logicNames)
        , privateReflectNames
        )
  where
    dependencyPairs = map (first GHC.unStableModule) $ HM.toList $ getDependencies dependencies

    mkLogicNameEnv names =
      LogicNameEnv
        { lneLHName = fromListSEnv [ (lhNameToResolvedSymbol n, n) | n <- names ]
        , lneReflected = GHC.mkNameEnv [(rn, n) | n <- names, Just rn <- [maybeReflectedLHName n]]
        }

unionAliasEnvs :: forall a. [InScopeEnv a] -> InScopeEnv a
unionAliasEnvs =
    coerce .
    -- We make sure that the module alias and the 'LHName' effectively disambiguate
    -- the occurrence of a symbol. This is because the same name can come from
    -- several imported modules.
    HM.map (nubBy (\(alias1, (_, n1, _)) (alias2, (_, n2, _)) -> alias1 == alias2 && n1 == n2)) .
    foldl' (HM.unionWith (++)) HM.empty .
    coerce @_ @[HM.HashMap Symbol [(GHC.ModuleName, (GHC.Module, LHName, a))]]

-- | Builds a symbol lookup environment from a list of names associated with the
-- module they were extracted from, adding any import aliases that module may
-- have within the current module (if it was imported directly).
mkAliasEnv:: GHC.Module -> GHC.ImportedMods -> (GHC.Module, [(LHName, a)]) -> InScopeEnv a
mkAliasEnv thisModule impMods (m, lhnames) =
    let aliases = moduleAliases thisModule impMods m
     in fromListSEnv
          -- Note that when building a name environment for the current module
          -- we might process unresolved names here.
          [ (LH.dropModuleNames $ getLHNameSymbol lhname
            , map (,(m, lhname, x)) aliases)
          | (lhname, x) <- lhnames
          ]

-- | Produces the list of aliases a module is imported with.
-- The first parameter holds the reference to the current module.
-- Transitive dependencies get an empty alias list.
moduleAliases :: GHC.Module -> GHC.ImportedMods -> GHC.Module -> [GHC.ModuleName]
moduleAliases thisModule impMods m =
    case Map.lookup m impMods of
      -- Aliases for imported modules.
      Just impBys -> concatMap imvAliases $ GHC.importedByUser impBys
      Nothing
        | thisModule == m ->
          -- Aliases for the current module.
          [GHC.moduleName m, GHC.mkModuleName ""]
        | otherwise ->
          -- For LHAssumptions modules, use the aliases of the unsuffixed module.
          concatMap imvAliases $ GHC.importedByUser $
            concat $ maybeToList $ do
              pString <- dropLHAssumptionsSuffix
              pMod <- findDependency pString
              Map.lookup pMod impMods
  where
    dropLHAssumptionsSuffix =
      let mString = GHC.moduleNameString (GHC.moduleName m)
          sfx = "_LHAssumptions"
       in if isSuffixOf sfx mString then
            Just $ dropEnd (length sfx) mString
          else
            Nothing

    findDependency ms =
      find ((ms ==) . GHC.moduleNameString . GHC.moduleName) $
      Map.keys impMods

    imvAliases imv
      | GHC.imv_qualified imv = [GHC.imv_name imv]
      | otherwise = [GHC.imv_name imv, GHC.mkModuleName ""]

collectLiftedSpecLogicNames :: LiftedSpec -> [LHName]
collectLiftedSpecLogicNames sp = concat
    [ map fst (HS.toList $ liftedExpSigs sp)
    , map (val . msName) (HM.elems $ liftedMeasures sp)
    , map (val . msName) (HM.elems $ liftedCmeasures sp)
    , map (val . msName) (HS.toList $ liftedOmeasures sp)
    , map fst $ concatMap DataDecl.dcFields $ concat $
        mapMaybe DataDecl.tycDCons $
        HS.toList $ liftedDataDecls sp
    , map  (val . rtName) $ HS.toList $ liftedEaliases sp
    ]

-- | Resolves names in the logic namespace
--
-- Returns the renamed spec.
-- Adds in the monadic state the errors about ambiguous or missing names, and
-- the names of data constructors that are found during renaming.
resolveLogicNames
  :: Config
  -> GHC.Module
  -> InScopeNonReflectedEnv
  -> GHC.GlobalRdrEnv
  -> LogicMap
  -> LocalVars
  -> LogicNameEnv
  -> HS.HashSet LocSymbol
  -> HS.HashSet Symbol
  -> BareSpecParsed
  -> State RenameOutput BareSpecLHName
resolveLogicNames cfg thisModule env globalRdrEnv lmap0 localVars lnameEnv privateReflectNames depsInlinesAndDefines sp = do
    -- Instance measures must be defined for names of class measures.
    -- The names of class measures should be in @env@
    imeasures <- mapM (mapMeasureNamesM resolveIMeasLogicName) (imeasures sp)
    emapSpecM
      (bscope cfg)
      (map localVarToSymbol . maybe [] lvdLclEnv . (GHC.lookupNameEnv (lvNames localVars) <=< getLHGHCName))
      resolveLogicName
      (emapBareTypeVM (bscope cfg) resolveLogicName)
      sp {imeasures}
  where
    resolveIMeasLogicName lx =
      case val lx of
        LHNUnresolved LHLogicName s -> (<$ lx) <$> resolveLogicName [] (s <$ lx)
        _ -> panic (Just $ LH.fSrcSpan lx) $ "unexpected name: " ++ show lx

    localVarToSymbol = F.symbol . GHC.occNameString . GHC.nameOccName . GHC.varName

    resolveLogicName :: [Symbol] -> LocSymbol -> State RenameOutput LHName
    resolveLogicName ss ls
        -- The name is local
      | elem s ss = return $ makeLocalLHName s
      | otherwise =
        case lookupInScopeEnv env s of
          Left alts ->
            -- If names are not in the environment, they must be data constructors,
            -- or they must be reflected functions, or they must be in the logicmap.
            case resolveClassMethodName ls `mplus` resolveDataConName ls `mplus` resolveVarName lmap0 ls of
              Just m -> m
              Nothing
                | elem s wiredInNames ->
                  return $ makeLocalLHName s
                | otherwise -> do
                    addError $ errResolve alts "logic name" "Cannot resolve name" ls
                    return $ makeLocalLHName s
          Right [(_, lhname, _)] -> pure lhname
          -- In case of multiple matches, we give precedence to locally defined
          -- logic entities for the user to be able to overwrite them.
          -- TODO: When a mechanism allowing to specify explicitly which logic names
          -- are imported is in place, we should cosider notifying the ambiguity directly.
          Right names ->
            case filter ((== thisModule) . logicNameOriginModule . Misc.snd3) names of
              [(_, lhname, _)] -> pure lhname
              _ -> do addError $ errDupInScopeNames ls names
                      return $ makeLocalLHName s
      where
        s = val ls
        wiredInNames =
           map fst wiredSortedSyms ++
           map (lhNameToResolvedSymbol . fst) (concatMap (DataDecl.dcpTyArgs . val) wiredDataCons)
        errDupInScopeNames locSym inScopeNames =
          ErrDupNames
            (LH.fSrcSpan locSym)
            "non-reflected logic entity"
            (pprint (val locSym))
            [ pprint (lhNameToResolvedSymbol n) PJ.<+>
              PJ.text
                ("imported from " ++ GHC.moduleNameString (GHC.moduleName m))
            | (m, n, _) <- inScopeNames
            ]

    resolveDataConName ls
      | unqualifiedS == ":" = Just $
        return $ makeLogicLHName unqualifiedS (GHC.nameModule consDataConName) (Just consDataConName)
      | unqualifiedS == "[]" = Just $
        return $ makeLogicLHName unqualifiedS (GHC.nameModule nilDataConName) (Just nilDataConName)
      | Just arity <- isTupleDC (symbolText s) = Just $
          let dcName = tupleDataConName arity
           in return $ makeLogicLHName s (GHC.nameModule dcName) (Just dcName)
      where
        unqualifiedS = LH.dropModuleNames s
        nilDataConName = GHC.getName $ GHC.dataConWorkId GHC.nilDataCon
        consDataConName = GHC.getName $ GHC.dataConWorkId GHC.consDataCon
        tupleDataConName = GHC.getName . GHC.dataConWorkId . GHC.tupleDataCon GHC.Boxed
        s = val ls
        isTupleDC t
          | Text.isPrefixOf "(" t && Text.isSuffixOf ")" t &&
            Text.all (== ',') (Text.init $ Text.tail t)
          = Just $ Text.length t - 2
          | otherwise
          = Nothing
    resolveDataConName s =
      case GHC.lookupGRE globalRdrEnv (mkLookupGRE (LHDataConName LHAnyModuleNameF) $ val s) of
        [e] -> do
          let n = GHC.greName e
          Just $ do
            let lhName = makeLogicLHName (symbol $ GHC.getOccString n) (GHC.nameModule n) (Just n)
            addName lhName
            addDataConsName lhName
            return lhName
        [] ->
          Nothing
        es ->
          Just $ do
            addError
              (ErrDupNames
                 (LH.fSrcSpan s)
                 "data constructor"
                 (pprint $ val s)
                 (map (PJ.text . GHC.showPprUnsafe) es)
              )
            return $ makeLocalLHName $ val s
    resolveClassMethodName s =
      case GHC.lookupGRE globalRdrEnv (mkLookupGRE (LHVarName LHAnyModuleNameF) $ val s) of
        [e] ->
          case (GHC.greInfo e, GHC.greParent_maybe e) of
            (GHC.Vanilla, Just pName) ->
              if isClassTyCon pName
              then Just $ do
                let n = GHC.greName e
                let lhName = makeLogicLHName (symbol $ GHC.getOccString n) (GHC.nameModule n) Nothing
                addName lhName
                return lhName
              else Nothing
            _ -> Nothing
        _ -> Nothing

    isClassTyCon parentName =
      case GHC.lookupGRE globalRdrEnv (mkLookupGRE (LHTcName LHAnyModuleNameF) (symbol $ GHC.occNameString $ GHC.nameOccName parentName)) of
        [parentGre] ->
          case GHC.greInfo parentGre of
            GHC.IAmTyCon GHC.ClassFlavour -> True
            _ -> False
        _ -> False

    -- Resolves names of reflected functions or names in the logic map
    --
    -- Names of reflected functions are resolved here because, to be in scope,
    -- we ask the corresponding Haskell name to be in scope. In contrast, the
    -- @InScopeNonReflectedEnv@ indicates where the reflect annotations were
    -- imported from, but not where the Haskell names were imported from.
    resolveVarName lmap s = do
      let gres =
            GHC.lookupGRE globalRdrEnv $
            mkLookupGRE (LHVarName LHAnyModuleNameF) (val s)
          refls = mapMaybe (findReflection . GHC.greName) gres
      case refls of
        [lhName] -> Just $ return lhName
        _ | HS.member s privateReflectNames
          -> Just $ return $ makeLocalLHName (val s)
          | otherwise
          -> case gres of
          [e] -> do
            let n = GHC.greName e
            -- See [NOTE:EXPRESSION-ALIASES]
            if HM.member (symbol n) (lmSymDefs lmap) || HS.member (symbol n) depsInlinesAndDefines then
              Just $ do
                let lhName = makeLogicLHName (symbol $ GHC.getOccString n) (GHC.nameModule n) Nothing
                addName lhName
                return lhName
            else
              Nothing
          [] ->
            Nothing
          es ->
            Just $ do
              addError
                 (ErrDupNames
                   (LH.fSrcSpan s)
                   "variable"
                   (pprint $ val s)
                   (map (PJ.text . GHC.showPprUnsafe) es)
                 )
              return $ makeLocalLHName $ val s

    findReflection :: GHC.Name -> Maybe LHName
    findReflection n = GHC.lookupNameEnv (lneReflected lnameEnv) n

mapMeasureNamesM :: Monad m => (Located LHName -> m (Located LHName)) -> MeasureV v ty ctor -> m (MeasureV v ty ctor)
mapMeasureNamesM f m = do
    msName <- f (msName m)
    msEqns <- mapM mapDefNameM (msEqns m)
    return m {msName, msEqns}
  where
    mapDefNameM d = do
      measure <- f (measure d)
      return d {measure}

mapDataDeclFieldNamesM :: Monad m => (LHName -> m LHName) -> DataDecl.DataDeclP v ty -> m (DataDecl.DataDeclP v ty)
mapDataDeclFieldNamesM f d = do
    tycDCons <- traverse (mapM (mapDataCtorFieldsM f)) (DataDecl.tycDCons d)
    return d{DataDecl.tycDCons}
  where
    mapDataCtorFieldsM :: Monad m => (LHName -> m LHName) -> DataDecl.DataCtorP ty -> m (DataDecl.DataCtorP ty)
    mapDataCtorFieldsM f1 c = do
      dcFields <- mapM (\(n, t) -> (, t) <$> f1 n) (DataDecl.dcFields c)
      return c{DataDecl.dcFields}

toBareSpecLHName :: Config -> LogicNameEnv -> BareSpec -> BareSpecLHName
toBareSpecLHName cfg lenv sp0 = runIdentity $ go sp0
  where
    -- This is implemented with a monadic traversal to reuse the logic
    -- that collects the local symbols in scope.
    go :: BareSpec -> Identity BareSpecLHName
    go sp =
      emapSpecM
        (bscope cfg)
        (const [])
        symToLHName
        (emapBareTypeVM (bscope cfg) symToLHName)
        sp

    symToLHName = symbolToLHName "toBareSpecLHName" lenv unhandledNames

    unhandledNames = HS.fromList $ map fst $ expSigs sp0

-- | Uses the logic name environment to convert a resolved 'Symbol' to 'LHName'.
-- Symbols not present in the environment correspond to local symbols (e.g.
-- bounded variables) or are explicitly left unhandled.
symbolToLHName :: String -> LogicNameEnv -> HS.HashSet Symbol -> [Symbol] -> Symbol -> Identity LHName
symbolToLHName caller lenv unhandledNames ss s
  | elem s ss = return $ makeLocalLHName s
  | otherwise =
    case lookupSEnv s (lneLHName lenv) of
      Nothing -> do
        unless (HS.member s unhandledNames) $
          panic Nothing $ caller ++ ": cannot find " ++ show s
        return $ makeLocalLHName s
      Just lhname -> return lhname
