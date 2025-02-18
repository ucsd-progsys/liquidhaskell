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
-- might be referred in refinment types, type aliases or other annotations.
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
--   a 'BareSpecLHName', where 'Symbol's are replaced with 'LHName'. At
--   the moment most LHNames are just wrappers over the symbols. As name
--   resolution is implemented for logic names, the wrappers will be
--   replaced with the actual result of name resolution.
--
-- 'BareSpecLHName' has a bijection to 'BareSpec' via a 'LogicNameEnv'
-- which allows to convert 'LHName' to an unambiguous form of 'Symbol'
-- and back. The bijection is implemented with the functions 'toBareSpecLHName'
-- and 'fromBareSpecLHName'. This allows to use liquid-fixpoint functions
-- unmodified as they will continue to operate on (now unambiguous) Symbols.
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
  , LogicNameEnv(..)
  ) where

import qualified Liquid.GHC.API         as GHC hiding (Expr, panic)
import qualified Language.Haskell.Liquid.GHC.Interface   as LH
import qualified Language.Haskell.Liquid.GHC.Misc        as LH
import           Language.Haskell.Liquid.Types.Names
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.RTypeOp

import           Control.Monad ((<=<), mplus, unless, void)
import           Control.Monad.Identity
import           Control.Monad.State.Strict
import           Data.Bifunctor (first)
import qualified Data.Char                               as Char
import           Data.Coerce (coerce)
import           Data.Data (Data, gmapT)
import           Data.Generics (extT)


import qualified Data.HashSet                            as HS
import qualified Data.HashMap.Strict                     as HM
import           Data.List (find, isSuffixOf, nubBy)
import           Data.List.Extra (dropEnd)
import           Data.Maybe (fromMaybe, listToMaybe, mapMaybe, maybeToList)
import qualified Data.Text                               as Text
import qualified GHC.Types.Name.Occurrence

import           Language.Fixpoint.Types as F hiding (Error, panic)
import qualified Language.Haskell.Liquid.Bare.Resolve as Resolve
import           Language.Haskell.Liquid.Bare.Types (LocalVars(lvNames), LocalVarDetails(lvdLclEnv))
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
-- It doesn't matter at the moment in which module a type alias is defined.
-- Type alias names cannot be qualified at the moment, and therefore their
-- names identify them uniquely.
collectTypeAliases
  :: GHC.Module
  -> BareSpecParsed
  -> TargetDependencies
  -> HM.HashMap Symbol (GHC.Module, RTAlias Symbol ())
collectTypeAliases m spec deps =
    let bsAliases = [ (rtName a, (m, void a)) | a <- map val (aliases spec) ]
        depAliases =
          [ (rtName a, (GHC.unStableModule sm, void a))
          | (sm, lspec) <- HM.toList (getDependencies deps)
          , a <- map val (HS.toList $ liftedAliases lspec)
          ]
     in
        HM.fromList $ bsAliases ++ depAliases

collectExprAliases
  :: BareSpecParsed
  -> TargetDependencies
  -> HS.HashSet Symbol
collectExprAliases spec deps =
    let bsAliases = HS.fromList $ map (rtName . val) (ealiases spec)
        depAliases =
          [ HS.map (rtName . val) $ liftedEaliases lspec
          | (_, lspec) <- HM.toList (getDependencies deps)
          ]
     in
        HS.unions $ bsAliases : depAliases

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
resolveLHNames cfg thisModule localVars impMods globalRdrEnv bareSpec0 dependencies = do
    let ((bs, logicNameEnv, lmap2), ro) =
          flip runState RenameOutput {roErrors = [], roUsedNames = [], roUsedDataCons = mempty} $ do
            -- A generic traversal that resolves names of Haskell entities
            sp1 <- mapMLocLHNames (\l -> (<$ l) <$> resolveLHName l) $
                     fixExpressionArgsOfTypeAliases taliases bareSpec0
            -- Data decls contain fieldnames that introduce measures with the
            -- same names. We resolved them before constructing the logic
            -- environment.
            dataDecls <- mapM (mapDataDeclFieldNamesM resolveFieldLogicName) (dataDecls sp1)
            let sp2 = sp1 {dataDecls}

            es0 <- gets roErrors
            if null es0 then do

              -- Now we do a second traversal to resolve logic names
              let (inScopeEnv, logicNameEnv0, privateReflectNames, unhandledNames) =
                    makeLogicEnvs impMods thisModule sp2 dependencies
              -- Add resolved local defines to the logic map
                  lmap1 =
                    lmap <> mkLogicMap (HM.fromList $
                                         (\(k , v) ->
                                             let k' = lhNameToResolvedSymbol <$> k in
                                             (F.val k', (val <$> v) { lmVar = k' }))
                                         <$> defines sp2)
              sp3 <- fromBareSpecLHName <$>
                       resolveLogicNames
                         cfg
                         inScopeEnv
                         globalRdrEnv
                         unhandledNames
                         lmap1
                         localVars
                         logicNameEnv0
                         privateReflectNames
                         allEaliases
                         sp2
              dcs <- gets roUsedDataCons
              return (sp3 {usedDataCons = dcs} , logicNameEnv0, lmap1)
            else
              return ( error "resolveLHNames: invalid spec"
                     , error "resolveLHNames: invalid logic environment"
                     , error "resolveLHNames: invalid logic map")
        logicNameEnv' = extendLogicNameEnv logicNameEnv (roUsedNames ro)
    if null (roErrors ro) then
      Right (bs, logicNameEnv', lmap2)
    else
      Left (roErrors ro)
  where
    taliases = collectTypeAliases thisModule bareSpec0 dependencies
    allEaliases = collectExprAliases bareSpec0 dependencies

    -- add defines from dependencies to the logical map
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

    resolveLHName lname =
      case val lname of
        LHNUnresolved LHTcName s
          | isTuple s ->
            pure $ LHNResolved (LHRGHC $ GHC.tupleTyConName GHC.BoxedTuple (tupleArity s)) s
          | isList s ->
            pure $ LHNResolved (LHRGHC GHC.listTyConName) s
          | s == "*" ->
            pure $ LHNResolved (LHRGHC GHC.liftedTypeKindTyConName) s
          | otherwise ->
            case HM.lookup s taliases of
              Just (m, _) -> pure $ LHNResolved (LHRLogic $ LogicName s m Nothing) s
              Nothing -> lookupGRELHName LHTcName lname s listToMaybe
        LHNUnresolved ns@(LHVarName lcl) s
          | isDataCon s ->
              lookupGRELHName (LHDataConName lcl) lname s listToMaybe
          | otherwise ->
              lookupGRELHName ns lname s
                (fmap (either id GHC.getName) . Resolve.lookupLocalVar localVars (atLoc lname s))
        LHNUnresolved LHLogicNameBinder s ->
          pure $ makeLogicLHName s thisModule Nothing
        n@(LHNUnresolved LHLogicName _) ->
          -- This one will be resolved by resolveLogicNames
          pure n
        LHNUnresolved ns s -> lookupGRELHName ns lname s listToMaybe
        n -> pure n

    lookupGRELHName ns lname s localNameLookup =
      case maybeDropImported ns $ GHC.lookupGRE globalRdrEnv (mkLookupGRE ns s) of
        [e] -> do
          let n = GHC.greName e
              n' = fromMaybe n $ localNameLookup [n]
          pure $ LHNResolved (LHRGHC n') s
        es@(_:_) -> do
          let topLevelNames = map GHC.greName es
          case localNameLookup topLevelNames of
            Just n | notElem n topLevelNames ->
              pure $ LHNResolved (LHRGHC n) s
            _ -> do
              addError
                (ErrDupNames
                   (LH.fSrcSpan lname)
                   (pprint s)
                   (map (PJ.text . GHC.showPprUnsafe) es)
                )
              pure $ val lname
        [] ->
          case localNameLookup [] of
            Just n' ->
              pure $ LHNResolved (LHRGHC n') s
            Nothing -> do
              addError
                (errResolve (nameSpaceKind ns) "Cannot resolve name" (s <$ lname))
              pure $ val lname

    maybeDropImported ns es
      | localNameSpace ns = filter GHC.isLocalGRE es
      | otherwise = es

    localNameSpace = \case
      LHDataConName lcl -> lcl == LHThisModuleNameF
      LHVarName lcl -> lcl == LHThisModuleNameF
      LHTcName -> False
      LHLogicNameBinder -> False
      LHLogicName -> False

    nameSpaceKind :: LHNameSpace -> PJ.Doc
    nameSpaceKind = \case
      LHTcName -> "type constructor"
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

errResolve :: PJ.Doc -> String -> LocSymbol -> Error
errResolve k msg lx = ErrResolve (LH.fSrcSpan lx) k (pprint (val lx)) (PJ.text msg)

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
      case GHC.lookupGRE globalRdrEnv (mkLookupGRE LHTcName s) of
        [e] -> Right $ LHNResolved (LHRGHC $ GHC.greName e) s <$ lx
        [] -> Left $ errResolve "type constructor" "Cannot resolve name" lx
        es -> Left $ ErrDupNames
                (LH.fSrcSpan lx)
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
      LHTcName -> GHC.SameNameSpace
      LHDataConName _ -> GHC.SameNameSpace
      LHVarName _ -> GHC.RelevantGREs
        { GHC.includeFieldSelectors = GHC.WantNormal
        , GHC.lookupVariablesForFields = True
        , GHC.lookupTyConsAsWell = False
        }
      LHLogicNameBinder -> panic Nothing "mkWhichGREs: unexpected namespace LHLogicNameBinder"
      LHLogicName -> panic Nothing "mkWhichGREs: unexpected namespace LHLogicName"

    mkGHCNameSpace = \case
      LHTcName -> GHC.tcName
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
      LHNUnresolved LHTcName s ->
        if elem s boundVars then
          LHNResolved (LHRLocal s) s
        else
          LHNUnresolved LHTcName s
      n ->
        error $ "resolveLHNames: Unexpected resolved name: " ++ show n

    -- Applies a function to the body of type aliases, passes to every call the
    -- arguments of the alias.
    updateAliases f spec =
       spec
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
  :: HM.HashMap Symbol (GHC.Module, RTAlias Symbol ())
  -> BareSpecParsed
  -> BareSpecParsed
fixExpressionArgsOfTypeAliases taliases =
    mapBareTypes go . resolveBoundVarsInTypeAliases
  where
    go :: BareTypeParsed -> BareTypeParsed
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

mapBareTypes :: (BareTypeParsed -> BareTypeParsed) -> BareSpecParsed -> BareSpecParsed
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
exprArg :: SourcePos -> String -> BareTypeParsed -> ExprV LocSymbol
exprArg l msg = notracepp ("exprArg: " ++ msg) . go
  where
    go :: BareTypeParsed -> ExprV LocSymbol
    go (RExprArg e)     = val e
    go (RVar (BTV x) _)       = EVar x
    go (RApp x [] [] _) = EVar (getLHNameSymbol <$> btc_tc x)
    go (RApp f ts [] _) = eApps (EVar (getLHNameSymbol <$> btc_tc f)) (go <$> ts)
    go (RAppTy t1 t2 _) = EApp (go t1) (go t2)
    go z                = panic sp $ Printf.printf "Unexpected expression parameter: %s in %s" (show $ parsedToBareType z) msg
    sp                  = Just (LH.sourcePosSrcSpan l)

-- | An environment of names in scope
--
-- For each symbol we have the aliases with which it is imported and the
-- name corresponding to each alias.
type InScopeNonReflectedEnv = SEnv [(GHC.ModuleName, (GHC.Module, LHName))]

-- | Looks the names in scope with the given symbol.
-- Returns a list of close but different symbols or a non empty list
-- with the matched names.
lookupInScopeNonReflectedEnv
  :: InScopeNonReflectedEnv -> Symbol -> Either [Symbol] [(GHC.Module, LHName)]
lookupInScopeNonReflectedEnv env s = do
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
-- aliases for the current module, the spec of the current module, and the specs
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
     , HS.HashSet Symbol
     )
makeLogicEnvs impAvails thisModule spec dependencies =
    let unqualify s =
          if s == LH.qualifySymbol (symbol $ GHC.moduleName thisModule) (LH.dropModuleNames s) then
            LH.dropModuleNames s
          else
            s

        -- Names should be removed from this list as they are supported
        -- by renaming.
        unhandledNames = HS.fromList $
          map unqualify unhandledNamesList ++ map (LH.qualifySymbol (symbol $ GHC.moduleName thisModule)) unhandledNamesList
        unhandledNamesList =
          map (rtName . val) (ealiases spec)
          ++ concatMap (map getLHNameSymbol . snd) unhandledLogicNames
        unhandledLogicNames =
          map (fmap collectUnhandledLiftedSpecLogicNames) dependencyPairs
        logicNames =
          (thisModule, thisModuleNames) :
          map (fmap collectLiftedSpecLogicNames) dependencyPairs
          ++ unhandledLogicNames
        thisModuleNames = concat
          [ [ reflectLHName thisModule (val n)
            | n <- concat
              [ map fst (asmReflectSigs spec)
              , HS.toList (reflects spec)
              , HS.toList (opaqueReflects spec)
              , HS.toList (inlines spec)
              , HS.toList (hmeas spec)
              ]
            ]
          , [ val (msName m) | m <- measures spec ]
          , [ val (msName m) | m <- cmeasures spec ]
          , map fst $
             concatMap DataDecl.dcFields $ concat $
             mapMaybe DataDecl.tycDCons $
             dataDecls spec
          ]
        privateReflectNames =
          mconcat $
            privateReflects spec : map (liftedPrivateReflects . snd) dependencyPairs
     in
        ( unionAliasEnvs $ map mkAliasEnv logicNames
        , mkLogicNameEnv (concatMap snd logicNames)
        , privateReflectNames
        , unhandledNames
        )
  where
    dependencyPairs = map (first GHC.unStableModule) $ HM.toList $ getDependencies dependencies

    mkAliasEnv (m, lhnames) =
      let aliases = moduleAliases m
       in fromListSEnv
            [ (s, map (,(m, lhname)) aliases)
              -- Note that only non-reflected names go to the InScope environment.
              -- See the local function resolveVarName for more details.
            | lhname@(LHNResolved (LHRLogic (LogicName s _ Nothing)) _) <- lhnames
            ]

    unionAliasEnvs :: [InScopeNonReflectedEnv] -> InScopeNonReflectedEnv
    unionAliasEnvs =
      coerce .
      HM.map (nubBy (\(alias1, (_, n1)) (alias2, (_, n2)) -> alias1 == alias2 && n1 == n2)) .
      foldl' (HM.unionWith (++)) HM.empty .
      coerce @_ @[HM.HashMap Symbol [(GHC.ModuleName, (GHC.Module, LHName))]]

    moduleAliases m =
      case GHC.lookupModuleEnv impAvails m of
        Just impBys -> concatMap imvAliases $ GHC.importedByUser impBys
        Nothing
          | thisModule == m ->
            -- Aliases for the current module
            [GHC.moduleName m, GHC.mkModuleName ""]
          | otherwise ->
            -- Use the aliases of the unsuffixed module
            concatMap imvAliases $ GHC.importedByUser $
              concat $ maybeToList $ do
                pString <- dropLHAssumptionsSuffix m
                pMod <- findDependency pString
                GHC.lookupModuleEnv impAvails pMod

    dropLHAssumptionsSuffix m =
      let mString = GHC.moduleNameString (GHC.moduleName m)
          sfx = "_LHAssumptions"
       in if isSuffixOf sfx mString then
            Just $ dropEnd (length sfx) mString
          else
            Nothing

    findDependency ms =
      find ((ms ==) . GHC.moduleNameString . GHC.moduleName) $
      GHC.moduleEnvKeys impAvails

    imvAliases imv
      | GHC.imv_qualified imv = [GHC.imv_name imv]
      | otherwise = [GHC.imv_name imv, GHC.mkModuleName ""]

    mkLogicNameEnv names =
      LogicNameEnv
        { lneLHName = fromListSEnv [ (lhNameToResolvedSymbol n, n) | n <- names ]
        , lneReflected = GHC.mkNameEnv [(rn, n) | n <- names, Just rn <- [maybeReflectedLHName n]]
        }

{- HLINT ignore collectUnhandledLiftedSpecLogicNames "Use ++" -}
collectUnhandledLiftedSpecLogicNames :: LiftedSpec -> [LHName]
collectUnhandledLiftedSpecLogicNames sp =
    map (makeLocalLHName . LH.dropModuleNames . rtName . val) $ HS.toList $ liftedEaliases sp

collectLiftedSpecLogicNames :: LiftedSpec -> [LHName]
collectLiftedSpecLogicNames sp = concat
    [ map fst (HS.toList $ liftedExpSigs sp)
    , map (val . msName) (HM.elems $ liftedMeasures sp)
    , map (val . msName) (HM.elems $ liftedCmeasures sp)
    , map fst $ concatMap DataDecl.dcFields $ concat $
        mapMaybe DataDecl.tycDCons $
        HS.toList $ liftedDataDecls sp
    ]

-- | Resolves names in the logic namespace
--
-- Returns the renamed spec.
-- Adds in the monadic state the errors about ambiguous or missing names, and
-- the names of data constructors that are found during renaming.
resolveLogicNames
  :: Config
  -> InScopeNonReflectedEnv
  -> GHC.GlobalRdrEnv
  -> HS.HashSet Symbol
  -> LogicMap
  -> LocalVars
  -> LogicNameEnv
  -> HS.HashSet LocSymbol
  -> HS.HashSet Symbol
  -> BareSpecParsed
  -> State RenameOutput BareSpecLHName
resolveLogicNames cfg env globalRdrEnv unhandledNames lmap0 localVars lnameEnv privateReflectNames allEaliases sp = do
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
        case lookupInScopeNonReflectedEnv env s of
          Left alts ->
            -- If names are not in the environment, they must be data constructors,
            -- or they must be reflected functions, or they must be in the logicmap.
            case resolveDataConName ls `mplus` resolveVarName lmap0 ls of
              Just m -> m
              Nothing
                | elem s wiredInNames ->
                  return $ makeLocalLHName s
                | otherwise -> do
                  unless (HS.member s unhandledNames) $
                    addError (errResolveLogicName ls alts)
                  return $ makeLocalLHName s
          Right [(_, lhname)] ->
            return lhname
          Right names -> do
            addError $
              ErrDupNames
                (LH.fSrcSpan ls)
                (pprint s)
                [ pprint (lhNameToResolvedSymbol n) PJ.<+>
                  PJ.text
                    ("imported from " ++ GHC.moduleNameString (GHC.moduleName m))
                | (m, n) <- names
                ]
            return $ makeLocalLHName s
      where
        s = val ls
        wiredInNames =
           map fst wiredSortedSyms ++
           map (lhNameToResolvedSymbol . fst) (concatMap (DataDecl.dcpTyArgs . val) wiredDataCons)

    errResolveLogicName s alts =
      ErrResolve
        (LH.fSrcSpan s)
        (PJ.text "logic name")
        (pprint $ val s)
        (if null alts then
           PJ.text "Cannot resolve name"
         else
           PJ.text "Cannot resolve name" PJ.$$
           PJ.sep (PJ.text "Maybe you meant one of:" : map pprint alts)
        )

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
                 (pprint $ val s)
                 (map (PJ.text . GHC.showPprUnsafe) es)
              )
            return $ makeLocalLHName $ val s

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
            -- TODO: The check for allEaliases should be redundant when
            -- ealiases are put in the logic environments
            if HM.member (symbol n) (lmSymDefs lmap) || HS.member (symbol n) allEaliases then
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
toBareSpecLHName cfg env sp0 = runIdentity $ go sp0
  where
    -- This is implemented with a monadic traversal to reuse the logic
    -- that collects the local symbols in scope.
    go :: BareSpec -> Identity BareSpecLHName
    go sp =
      emapSpecM
        (bscope cfg)
        (const [])
        symbolToLHName
        (emapBareTypeVM (bscope cfg) symbolToLHName)
        sp

    unhandledNames = HS.fromList $ map fst $ expSigs sp0

    symbolToLHName :: [Symbol] -> Symbol -> Identity LHName
    symbolToLHName ss s
      | elem s ss = return $ makeLocalLHName s
      | otherwise =
        case lookupSEnv s (lneLHName env) of
          Nothing -> do
            unless (HS.member s unhandledNames) $
              panic Nothing $ "toBareSpecLHName: cannot find " ++ show s
            return $ makeLocalLHName s
          Just lhname -> return lhname
