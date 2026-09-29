{-| This module re-exports all identifiers that LH needs
    from the GHC API.

The intended use of this module is to provide a quick look of what
GHC API features LH depends upon.

The transitive dependencies of this module shouldn't contain modules
from Language.Haskell.Liquid.* or other non-boot libraries. This makes
it easy to discover breaking changes in the GHC API.

-}

{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternSynonyms #-}

module Liquid.GHC.API (
    module Ghc
  ) where

import Liquid.GHC.API.Extra as Ghc
import Liquid.GHC.API.Compat as Ghc

import           GHC                  as Ghc
    ( Class
    , DataCon
    , DesugaredModule(DesugaredModule, dm_typechecked_module, dm_core_module)
    , DynFlags(backend, debugLevel, ghcLink, ghcMode, warningFlags)
    , FixityDirection(InfixN, InfixR)
    , FixitySig(FixitySig)
    , GenLocated(L)
    , GeneralFlag(..)
    , Ghc
    , GhcException(CmdLineError, ProgramError)
    , GhcLink(LinkInMemory)
    , GhcMode(CompManager)
    , GhcMonad
    , GhcPs
    , GhcRn
    , HsBndrKind(HsBndrNoKind)
    , HsBndrVar(HsBndrVar)
    , HsDecl(SigD)
    , HsExpr(ExprWithTySig, HsOverLit, HsVar)
    , HsGroup
    , HsModule(hsmodDecls)
    , HsOuterTyVarBndrs(HsOuterImplicit)
    , HsSigType(HsSig)
    , HsTyVarBndr(HsTvb)
    , HsType(HsAppTy, HsForAllTy, HsQualTy, HsTyVar, HsWildCardTy)
    , HsArg(HsValArg)
    , HsWildCardBndrs(HsWC)
    , Id
    , IdP
    , Kind
    , LHsDecl
    , LHsExpr
    , LHsType
    , LImportDecl
    , LexicalFixity(Prefix)
    , Located
    , LocatedN
    , LoadHowMuch(LoadAllTargets)
    , ModLocation(ml_hs_file)
    , ModSummary(ms_hspp_file, ms_hspp_opts, ms_location, ms_mod)
    , Module
    , ModuleName
    , Name
    , NamedThing
    , NamespaceSpecifier (NoNamespaceSpecifier)
    , ParsedModule(..)
    , PredType
    , RealSrcLoc
    , RealSrcSpan
    , RdrName
    , Severity(SevWarning)
    , Sig(InlineSig, FixSig, TypeSig)
    , SrcLoc
    , StrictnessMark
    , TyCon
    , TyThing(AConLike, ATyCon, AnId)
    , TyVar
    , TypecheckedModule(tm_checked_module_info, tm_internals_, tm_parsed_module)
    , classMethods
    , classSCTheta
    , coreModule
    , dataConTyCon
    , dataConFieldLabels
    , dataConWrapperType
    , desugarModule
    , emptyRnGroup
    , getLocA
    , getLogger
    , getName
    , getOccName
    , getSession
    , getSessionDynFlags
    , guessTarget
    , gopt
    , hsTypeToHsSigType
    , hsTypeToHsSigWcType
    , idDataCon
    , idType
    , ideclAs
    , ideclName
    , instanceDFunId
    , isClassOpId_maybe
    , isClassTyCon
    , isDictonaryId
    , isExternalName
    , isFamilyTyCon
    , isGoodSrcSpan
    , isLocalId
    , isNewTyCon
    , isPrimTyCon
    , isRecordSelector
    , isTypeSynonymTyCon
    , isVanillaDataCon
    , lookupName
    , load
    , mkHsApp
    , mkHsDictLet
    , mkHsForAllInvisTele
    , mkHsFractional
    , mkHsIntegral
    , mkHsLam
    , mkModuleName
    , mkSrcLoc
    , mkSrcSpan
    , moduleName
    , moduleNameString
    , moduleUnit
    , noLoc
    , parseDynamicFlags
    , runGhc
    , setSession
    , setSessionDynFlags
    , setTargets
    , SuccessFlag(Succeeded, Failed)
    , ms_mod_name
    , nameModule
    , nameSrcSpan
    , nlHsAppTy
    , nlHsFunTy
    , nlHsIf
    , nlHsTyConApp
    , nlHsTyVar
    , nlHsVar
    , nlList
    , nlVarPat
    , noAnn
    , noAnnSrcSpan
    , noExtField
    , noLocA
    , noSrcSpan
    , splitForAllTyCoVars
    , srcLocFile
    , srcLocCol
    , srcLocLine
    , srcSpanEndCol
    , srcSpanEndLine
    , srcSpanFile
    , srcSpanStartCol
    , srcSpanStartLine
    , synTyConDefn_maybe
    , synTyConRhs_maybe
    , tyConArity
    , tyConClass_maybe
    , tyConDataCons
    , tyConKind
    , tyConTyVars
    , typecheckModule
    , unLoc
    )

import GHC.Builtin.Names              as Ghc
    ( Uniquable
    , Unique
    , and_RDR
    , bindMName
    , eq_RDR
    , eqClassKey
    , eqClassName
    , ge_RDR
    , gt_RDR
    , fractionalClassKey
    , fractionalClassKeys
    , getUnique
    , hasKey
    , isStringClassName
    , itName
    , le_RDR
    , lt_RDR
    , negateName
    , not_RDR
    , numericClassKeys
    , ordClassKey
    , ordClassName
    , plus_RDR
    , times_RDR
    , varQual_RDR
    )
import GHC.Builtin.Types              as Ghc
    ( anyTy
    , boolTy
    , boolTyCon
    , boolTyConName
    , charDataCon
    , charTyCon
    , consDataCon
    , falseDataCon
    , falseDataConId
    , intDataCon
    , intTy
    , intTyCon
    , intTyConName
    , integerISDataCon
    , integerIPDataCon
    , integerINDataCon
    , liftedTypeKind
    , liftedTypeKindTyConName
    , listTyCon
    , listTyConName
    , zonkAnyTyCon
    , naturalTy
    , nilDataCon
    , stringTy
    , true_RDR
    , trueDataCon
    , trueDataConId
    , tupleDataCon
    , tupleTyCon
    , tupleTyConName
    , typeSymbolKind
    , unrestrictedFunTyConName
    )
import GHC.Builtin.Types.Prim         as Ghc
    ( isArrowTyCon
    , eqPrimTyCon
    , eqReprPrimTyCon
    , primTyCons
    )
import GHC.Builtin.Utils              as Ghc
    ( isNumericClass )
import GHC.Core                       as Ghc
    ( Alt(Alt)
    , AltCon(DEFAULT, DataAlt, LitAlt)
    , Arg
    , Bind(NonRec, Rec)
    , CoreAlt
    , CoreArg
    , CoreBind
    , CoreBndr
    , CoreExpr
    , CoreProgram
    , Expr(App, Case, Cast, Coercion, Lam, Let, Lit, Tick, Type, Var)
    , Unfolding(CoreUnfolding, DFunUnfolding, uf_tmpl)
    , bindersOf
    , bindersOfBinds
    , cmpAlt
    , collectArgs
    , collectArgsTicks
    , collectBinders
    , collectTyAndValBinders
    , collectTyBinders
    , flattenBinds
    , isId
    , isTypeArg
    , maybeUnfoldingTemplate
    , mkApps
    , mkLams
    , mkLets
    , mkTyApps
    , mkTyArg
    , rhssOfAlts
    , rhssOfBind
    )
import GHC.Core.Class                 as Ghc
    ( classAllSelIds
    , classBigSig
    , classOpItems
    , classSCSelIds
    , Class
       ( classKey
       , className
       , classTyCon
       , classTyVars
       )
    )
import GHC.Core.Coercion              as Ghc
    ( Role
    , Var
    , coercionKind
    , isCoVar
    , mkRepReflCo
    )
import GHC.Core.Coercion.Axiom        as Ghc
    ( coAxiomTyCon
    , isNewtypeAxiomRule_maybe
    )
import GHC.Core.ConLike               as Ghc
    ( ConLike(RealDataCon) )
import GHC.Core.DataCon               as Ghc
    ( FieldLabel(flSelector)
    , classDataCon
    , dataConExTyCoVars
    , dataConFullSig
    , dataConImplicitTyThings
    , dataConInstArgTys
    , dataConName
    , dataConOrigArgTys
    , dataConRepArgTys
    , dataConRepType
    , dataConRepStrictness
    , dataConTheta
    , dataConUnivTyVars
    , dataConWorkId
    , dataConWrapId
    , dataConWrapId_maybe
    , isTupleDataCon
    , promoteDataCon
    )
import GHC.Core.FamInstEnv            as Ghc
    ( FamFlavor(DataFamilyInst)
    , FamInst(FamInst, fi_flavor)
    , FamInstEnv
    , FamInstEnvs
    , emptyFamInstEnv
    , famInstEnvElts
    , topNormaliseType_maybe
    )
import GHC.Core.InstEnv               as Ghc
    ( ClsInst(is_cls, is_dfun, is_dfun_name, is_tys)
    , DFunId
    , InstEnvs
    , instEnvElts
    , instanceSig
    , lookupInstEnv
    )
import GHC.Core.Make                  as Ghc
    ( mkCoreApps
    , mkCoreConApps
    , mkCoreLams
    , mkCoreLets
    , pAT_ERROR_ID
    )
import GHC.Core.Predicate             as Ghc
    ( getClassPredTys_maybe
    , getClassPredTys
    , isPredTy
    , isSimplePredTy
    , isEqPred
    , isEqClassPred
    , isClassPred
    , isDictId
    , mkClassPred
    )
import GHC.Core.Reduction             as Ghc
    ( Reduction(Reduction) )
import GHC.Core.Subst                 as Ghc (emptySubst, extendCvSubst)
import GHC.Core.TyCo.Rep              as Ghc
    ( Coercion
    , FunTyFlag(FTF_T_T, FTF_C_T)
    , ForAllTyFlag(Required)
    , Coercion (AxiomCo, SymCo)
    , TyLit(CharTyLit, NumTyLit, StrTyLit)
    , Type
        ( AppTy
        , CastTy
        , CoercionTy
        , ForAllTy
        , FunTy
        , LitTy
        , TyConApp
        , TyVarTy
        , ft_af
        , ft_arg
        , ft_res
        )
    , UnivCoProvenance(PhantomProv, ProofIrrelProv)
    , mkForAllTys
    , mkFunTy
    , mkTyVarTy
    , mkTyVarTys
    )
import GHC.Core.TyCo.Compare          as Ghc (eqType, nonDetCmpType)
import GHC.Core.TyCo.Subst            as Ghc
    ( extendSubstInScope
    , extendSubstInScopeSet
    , substCo
    , zipTvSubst
    )
import GHC.Core.TyCon                 as Ghc
    ( TyConBinder
    , TyConBndrVis(AnonTCB)
    , isAlgTyCon
    , isBoxedTupleTyCon
    , isFamInstTyCon
    , isGadtSyntaxTyCon
    , isPromotedDataCon
    , isTupleTyCon
    , isVanillaAlgTyCon
    , mkPrimTyCon
    , newTyConEtadArity
    , newTyConRhs
    , tyConBinders
    , tyConDataCons_maybe
    , tyConFamInst_maybe
    , tyConName
    , tyConSingleDataCon_maybe
    )
import GHC.Core.Type                  as Ghc
    ( Specificity(SpecifiedSpec)
    , TyVarBinder
    , isTYPEorCONSTRAINT
    , dropForAlls
    , emptyTvSubstEnv
    , expandTypeSynonyms
    , irrelevantMult
    , isFunTy
    , isTyVar
    , isTyVarTy
    , pattern ManyTy
    , mkTvSubstPrs
    , mkTyConApp
    , newTyConInstRhs
    , piResultTys
    , splitAppTys
    , splitForAllForAllTyBinders
    , splitFunTy_maybe
    , splitFunTys
    , splitTyConApp
    , splitTyConApp_maybe
    , substTy
    , substTyWith
    , tyConAppArgs_maybe
    , tyConAppTyCon_maybe
    , tyVarKind
    , varType
    )
import GHC.Core.Unify                 as Ghc
    ( ruleMatchTyKiX, tcUnifyTy, tcMatchTy )
import GHC.Core.Utils                 as Ghc (exprType)
import GHC.Data.Bag                   as Ghc
    ( Bag, bagToList )
import GHC.Data.IOEnv                 as Ghc
    ( IOEnvFailure(..) )
import GHC.Data.FastString            as Ghc
    ( FastString
    , bytesFS
    , concatFS
    , fsLit
    , lexicalCompareFS
    , mkFastString
    , mkFastStringByteString
    , mkPtrString#
    , uniq
    , unpackFS
    )
import GHC.Data.Pair                  as Ghc
    ( Pair(Pair) )
import GHC.Driver.Config.Diagnostic as Ghc
    ( initDiagOpts
    , initDsMessageOpts
    , initIfaceMessageOpts
    )
import GHC.Driver.Plugins             as Ghc
    ( ParsedResult(..)
    , Plugins(staticPlugins)
    , PluginWithArgs(PluginWithArgs)
    , StaticPlugin(StaticPlugin)
    )
import GHC.Driver.Phases              as Ghc (Phase(StopLn))
import GHC.Driver.Pipeline            as Ghc (compileFile)
import GHC.Driver.Pipeline.Execute    as Ghc (runPhase)
import GHC.Driver.Pipeline.Phases     as Ghc (PhaseHook(PhaseHook), TPhase(T_HscPostTc))
import GHC.Driver.Hooks               as Ghc (Hooks(runPhaseHook))
import GHC.Fingerprint                as Ghc (Fingerprint(Fingerprint), fingerprintData)
import GHC.Driver.Session             as Ghc
    ( getDynFlags
    , gopt_set
    , gopt_unset
    , updOptLevel
    , xopt_set
    )
import GHC.Driver.Monad               as Ghc (withSession, reflectGhc, Session(..))
import GHC.HsToCore.Monad             as Ghc
    ( DsM, initDsTc, initDsWithModGuts, newUnique )
import GHC.Iface.Syntax               as Ghc
    ( IfaceAnnotation(IfaceAnnotation, ifAnnotatedValue) )
import GHC.Iface.Ext.Fields           as Ghc
    ( FieldName, readField, writeField, getExtensibleFields )
import GHC.Iface.Make                 as Ghc (mkFullIface)
import GHC.Plugins                    as Ghc
    ( Serialized(Serialized)
    , deserializeWithData
    , fromSerialized
    , toSerialized
    , defaultPlugin
    , emptyPlugins
    , Plugin(..)
    , CommandLineOption
    , purePlugin
    , extendIdSubst
    , extendIdSubstList
    , extendSubst
    , extendSubstList
    , extendTvSubst
    , extendTvSubstList
    , mkEmptySubst
    , substExpr
    , Subst
    )
import GHC.Core.FVs                   as Ghc
    ( exprFreeVars
    , exprFreeVarsList
    , orphNamesOfExprs
    , exprSomeFreeVarsList
    )
import GHC.Core.Opt.OccurAnal         as Ghc
    ( occurAnalysePgm )
import GHC.Core.TyCo.FVs              as Ghc (tyCoVarsOfCo, tyCoVarsOfType)
import GHC.Driver.Backend             as Ghc (backendName, interpreterBackend)
import GHC.Driver.Backend.Internal    as Ghc (BackendName(NoBackend))
import GHC.Driver.DynFlags            as Ghc
    ( DumpFlag(Opt_D_dump_timings)
    , dopt_set
    )
import GHC.Driver.Env                 as Ghc
    ( HscEnv(hsc_NC, hsc_unit_env, hsc_dflags, hsc_plugins, hsc_hooks, hsc_logger)
    , Hsc
    , hscSetFlags, hscUpdateFlags
    , hsc_HUG, lookupIfaceByModuleHsc
    )
import GHC.Driver.Main                as Ghc
    ( hscDesugar, hscMaybeWriteIface )
import GHC.Driver.Errors              as Ghc
    ( printMessages )
import GHC.Driver.Ppr                 as Ghc
    ( showPpr
    , showSDoc
    )
import GHC.Hs                         as Ghc
    ( HsParsedModule(..)
    , ClsInstDecl(cid_binds)
    , InstDecl(ClsInstD)
    , hsGroupInstDecls
    )
import GHC.HsToCore.Expr              as Ghc
    ( dsLExpr )
import GHC.Iface.Binary               as Ghc
    ( CompressionIFace(SafeExtraCompression)
    , TraceBinIFace(QuietBinIFace)
    , getWithUserData
    , putWithUserData
    )
import GHC.Iface.Errors.Ppr            as Ghc
    ( missingInterfaceErrorDiagnostic )
import GHC.Iface.Load                 as Ghc
    ( WhereFrom(ImportBySystem)
    , cannotFindModule
    , loadInterface
    )
import GHC.Rename.Expr                as Ghc (rnLExpr)
import GHC.Rename.Names               as Ghc
    ( renamePkgQual
    )
import GHC.Tc.Errors.Types            as Ghc
    ( mkTcRnUnknownMessage )
import GHC.Tc.Gen.Bind                as Ghc (tcValBinds)
import GHC.Tc.Gen.Expr                as Ghc (tcInferRho, tcInferSigma)
import GHC.Tc.Solver                  as Ghc
    ( InferMode(NoRestrictions)
    , captureTopConstraints
    , simplifyInfer
    , simplifyInteractive
    )
import GHC.Tc.Types                   as Ghc
    ( Env(env_top)
    , FrontendResult(FrontendTypecheck)
    , TcGblEnv
        ( tcg_anns
        , tcg_exports
        , tcg_imports
        , tcg_insts
        , tcg_mod
        , tcg_rdr_env
        , tcg_rn_decls
        , tcg_type_env
        , tcg_th_state
        )
    , TcM
    , TcRn
    )
import GHC.Tc.Types.Evidence          as Ghc
    ( TcEvBinds(EvBinds) )
import GHC.Tc.Types.Origin            as Ghc (lexprCtOrigin)
import GHC.Tc.Utils.Env               as Ghc
    ( tcGetInstEnvs )
import GHC.Tc.Utils.Monad             as Ghc
    ( captureConstraints
    , discardConstraints
    , getGblEnv
    , setGblEnv
    , getEnv
    , getTopEnv
    , failIfErrsM
    , failM
    , failWithTc
    , initIfaceTcRn
    , liftIO
    , addErrAt
    , addErrs
    , pushTcLevelM
    , reportDiagnostic
    , reportDiagnostics
    , updEnv
    , updTopEnv
    )
import GHC.Tc.Utils.TcType            as Ghc (tcSplitDFunTy, tcSplitMethodTy)
import GHC.Tc.Zonk.Type               as Ghc
    ( zonkTopLExpr )
import GHC.ThToHs as Ghc
    ( thRdrNameGuesses )
import GHC.Types.PkgQual              as Ghc
    ( PkgQual(NoPkgQual) )
import GHC.Types.Annotations          as Ghc
    ( AnnPayload
    , AnnTarget(ModuleTarget)
    , Annotation(Annotation, ann_target, ann_value)
    , findAnns
    )
import GHC.Types.Avail                as Ghc
    ( AvailInfo(Avail, AvailTC)
    , availNames
    , availsToNameSet
    )
import GHC.Types.Basic                as Ghc
    ( Arity
    , Boxity(Boxed)
    , DefMethSpec(VanillaDM)
    , PprPrec
    , PromotionFlag(NotPromoted)
    , TopLevelFlag(NotTopLevel)
    , TupleSort(BoxedTuple)
    , funPrec
    , InlinePragma(inl_act, inl_inline, inl_rule, inl_sat, inl_src)
    , isDeadOcc
    , isNoInlinePragma
    , isStrongLoopBreaker
    , noOccInfo
    , topPrec
    , TyConFlavour (..)
    )
import GHC.Types.CostCentre           as Ghc
    ( CostCentre(cc_loc)
    )
import GHC.Types.Error                as Ghc
    ( Messages(getMessages)
    , MessageClass(MCDiagnostic)
    , Diagnostic
    , DiagnosticReason(WarningWithoutFlag)
    , MsgEnvelope(errMsgSpan)
    , ResolvedDiagnosticReason(ResolvedDiagnosticReason)
    , defaultDiagnosticOpts
    , errorsOrFatalWarningsFound
    , mkPlainError
    )
import GHC.Types.Fixity               as Ghc
    ( Fixity(Fixity) )
import GHC.Types.Id                   as Ghc
    ( idDetails
    , isDFunId
    , idInfo
    , idOccInfo
    , isConLikeId
    , isDataConId_maybe
    , idInlinePragma
    , modifyIdInfo
    , mkExportedLocalId
    , mkUserLocalOrCoVar
    , realIdUnfolding
    , setIdInfo
    )
import GHC.Types.Id.Info              as Ghc
    ( CafInfo(NoCafRefs)
    , IdDetails(ClassOpId, DataConWorkId, DataConWrapId, RecSelId, VanillaId)
    , IdInfo(occInfo, realUnfoldingInfo)
    , cafInfo
    , inlinePragInfo
    , mayHaveCafRefs
    , realUnfoldingInfo
    , setCafInfo
    , setOccInfo
    , vanillaIdInfo
    )
import GHC.Types.Literal              as Ghc
    ( LitNumType(LitNumInt)
    , Literal(LitChar, LitDouble, LitFloat, LitNullAddr, LitNumber, LitString)
    , literalType
    )
import GHC.Types.Name                 as Ghc
    ( OccName
    , getOccString
    , getSrcSpan
    , isInternalName
    , isSystemName
    , isTupleTyConName
    , mkInternalName
    , mkSystemName
    , mkTcOcc
    , mkTyVarOcc
    , mkVarOcc
    , mkVarOccFS
    , nameModule_maybe
    , nameNameSpace
    , nameOccName
    , nameSrcLoc
    , nameStableString
    , nameUnique
    , occNameFS
    , occNameString
    , stableNameCmp
    )
import GHC.Types.Name.Env             as Ghc
    ( NameEnv
    , lookupNameEnv
    , mkNameEnv
    , mkNameEnvWith
    )
import GHC.Types.Name.Set             as Ghc
    ( NameSet
    , elemNameSet
    , nameSetElemsStable
    )
import GHC.Types.Name.Cache           as Ghc (NameCache)
import GHC.Types.Name.Occurrence      as Ghc
    ( NameSpace
    , isDerivedOccName
    , isFieldNameSpace
    , mkOccName
    , dataName
    , tcName
    )
import GHC.Types.Name.Reader          as Ghc
    ( FieldsOrSelectors(WantNormal)
    , GlobalRdrEnv
    , GREInfo (..)
    , ImpItemSpec(ImpAll)
    , LookupGRE(LookupOccName, LookupRdrName)
    , WhichGREs
        ( SameNameSpace
        , RelevantGREs
        , includeFieldSelectors
        , lookupTyConsAsWell
        , lookupVariablesForFields
        )
    , getRdrName
    , globalRdrEnvElts
    , greName
    , greInfo
    , greParent_maybe
    , isLocalGRE
    , lookupGRE
    , lookupGRE_Name
    , mkQual
    , mkRdrQual
    , mkRdrUnqual
    , mkVarUnqual
    , mkUnqual
    , nameRdrName
    , noUserRdr
    )
import GHC.Types.SourceError          as Ghc
    ( SourceError
    , srcErrorMessages
    )
import GHC.Types.SourceText           as Ghc
    ( SourceText(SourceText,NoSourceText)
    , mkIntegralLit
    , mkTHFractionalLit
    )
import GHC.Types.SrcLoc               as Ghc
    ( SrcSpan(RealSrcSpan, UnhelpfulSpan)
    , UnhelpfulSpanReason
        ( UnhelpfulGenerated
        , UnhelpfulInteractive
        , UnhelpfulNoLocationInfo
        , UnhelpfulOther
        , UnhelpfulWiredIn
        )
    , combineSrcSpans
    , isSubspanOf
    , mkGeneralSrcSpan
    , mkRealSrcLoc
    , mkRealSrcSpan
    , realSrcSpanStart
    , srcSpanFileName_maybe
    , srcSpanToRealSrcSpan
    )
import GHC.Types.Tickish              as Ghc (CoreTickish, GenTickish(..))
import GHC.Types.TypeEnv              as Ghc
    ( TypeEnv
    , lookupTypeEnv
    , mkTypeEnv
    , plusTypeEnv
    )
import GHC.Types.Unique               as Ghc
    ( getKey, mkUnique )
import GHC.Types.Unique.Set           as Ghc (mkUniqSet)
import GHC.Types.Unique.Supply        as Ghc
    ( MonadUnique, getUniqueM )
import GHC.Types.Var                  as Ghc
    ( VarBndr(Bndr)
    , binderVar
    , mkLocalVar
    , mkTyVar
    , setVarName
    , setVarType
    , setVarUnique
    , varName
    , varUnique
    )
import GHC.Types.Var.Env              as Ghc
    ( emptyInScopeSet, mkInScopeSet, mkRnEnv2 )
import GHC.Types.Var.Set              as Ghc
    ( VarSet
    , elemVarSet
    , emptyVarSet
    , extendVarSet
    , extendVarSetList
    , unionVarSet
    , unitVarSet
    )
import GHC.Unit.Env                   as Ghc
    ( UnitEnv(ue_eps), ue_hpt )
import GHC.Unit.External              as Ghc
    ( ExternalPackageState (eps_ann_env)
    , ExternalUnitCache(euc_eps)
    )
import GHC.Unit.Finder                as Ghc
    ( FindResult(Found, NoPackage, FoundMultiple, NotFound)
    , findExposedPackageModule
    , findImportedModule
    , findPluginModule
    )
import GHC.Unit.Home.ModInfo          as Ghc
    ( HomeModInfo(hm_iface) )
import GHC.Unit.Home.Graph            as Ghc (lookupHugByModule)
import GHC.Unit.Home.PackageTable     as Ghc
    ( HomePackageTable, lookupHpt )
import GHC.Unit.Module                as Ghc
    ( GenWithIsBoot(gwib_isBoot, gwib_mod)
    , IsBootInterface(NotBoot, IsBoot)
    , ModuleNameWithIsBoot
    , UnitId
    , lookupModuleEnv
    , stableModuleCmp
    , fsToUnit
    , mkModuleNameFS
    , moduleEnvKeys
    , moduleNameFS
    , moduleStableString
    , toUnitId
    , unitString
    )
import GHC.Unit.Module.Deps       as Ghc
    ( ImportAvails(imp_mods), Usage(UsagePackageModule) )
import GHC.Unit.Module.ModIface       as Ghc
    ( ModIface, ModIface_, IfaceSelfRecomp(mi_sr_usages)
    , pattern ModIface
    , emptyFullModIface, emptyPartialModIface
    , mi_anns, mi_exports, mi_module, mi_mod_hash, mi_self_recomp_info
    , mi_decls, mi_simplified_core, mi_mod_info, mi_deps, mi_fixities
    , mi_warns, mi_defaults, mi_insts, mi_fam_insts, mi_rules, mi_trust
    , mi_trust_pkg, mi_complete_matches, mi_docs, mi_top_env, mi_ext_fields
    , mi_sig_of, mi_hsc_src, mi_iface_hash, mi_public, mi_abi_hashes
    , mi_ext_fields, mi_hi_bytes, mi_fix_fn, mi_hash_fn, mi_decl_warn_fn
    , mi_export_warn_fn
    , set_mi_decls, set_mi_simplified_core, set_mi_mod_info, set_mi_deps
    , set_mi_exports, set_mi_fixities, set_mi_warns, set_mi_anns
    , set_mi_defaults, set_mi_insts, set_mi_fam_insts, set_mi_rules
    , set_mi_trust, set_mi_trust_pkg, set_mi_complete_matches, set_mi_docs
    , set_mi_top_env, set_mi_ext_fields, set_mi_self_recomp
    )
import GHC.Unit.Module.Status         as Ghc
    ( HscBackendAction(HscRecomp, hscs_partial_iface, HscUpdate) )
import GHC.Unit.Module.Imported       as Ghc
    ( ImportedMods
    , ImportedModsVal(imv_name, imv_qualified)
    , importedByUser
    )
import GHC.Unit.Module.ModGuts        as Ghc
    ( ModGuts
      ( mg_binds
      , mg_exports
      , mg_fam_inst_env
      , mg_inst_env
      , mg_module
      , mg_tcs
      , mg_usages
      )
    )
import GHC.Unit.Types                 as Ghc
    ( moduleUnitId
    , unitIdString
    , mainUnit, mkModule
    )
import GHC.Types.ForeignStubs         as Ghc (ForeignStubs(NoStubs))
import GHC.Utils.Binary               as Ghc
    ( Binary(get, put_)
    , getByte
    , openBinMem
    , putByte
    , unsafeUnpackBinBuffer
    , withBinBuffer
    )
import GHC.Utils.Error                as Ghc (pprLocMsgEnvelope, withTiming)
import GHC.Utils.Logger               as Ghc
    ( LogFlags
    , Logger(logFlags)
    , putLogMsg
    , log_set_dopt
    , updateLogFlags
    )
import GHC.Utils.Outputable           as Ghc hiding ((<>))
import GHC.Utils.Panic                as Ghc (panic, throwGhcException, throwGhcExceptionIO)
import GHC.Utils.Misc                 as Ghc (lengthAtLeast)
