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

import           GHC                  as Ghc
    ( Class
    , DataCon
    , DesugaredModule(DesugaredModule, dm_typechecked_module, dm_core_module)
    , DynFlags(backend, debugLevel, ghcLink, ghcMode, warningFlags)
    , FixityDirection(InfixN, InfixR)
    , FixitySig(FixitySig)
    , GenLocated(L)
    , GeneralFlag
        ( Opt_Haddock
        , Opt_InsertBreakpoints
        , Opt_KeepRawTokenStream
        , Opt_IgnoreInterfacePragmas
        )
    , Ghc
    , GhcException(CmdLineError, ProgramError)
    , GhcLink(LinkInMemory)
    , GhcMode(CompManager)
    , GhcMonad
    , GhcPs
    , GhcRn
    , HsDecl(SigD)
    , HsExpr(ExprWithTySig, HsOverLit, HsVar)
    , HsModule(hsmodDecls)
    , HsOuterTyVarBndrs(HsOuterImplicit)
    , HsSigType(HsSig)
    , HsTyVarBndr(UserTyVar)
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
    , ModIface_(mi_anns, mi_exports, mi_globals, mi_module)
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
    , getLocA
    , getLogger
    , getName
    , getOccName
    , getSession
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
    , mkHsApp
    , mkHsDictLet
    , mkHsForAllInvisTele
    , mkHsFractional
    , mkHsIntegral
    , mkHsLam
    , mkModuleName
    , mkSrcLoc
    , mkSrcSpan
    , modInfoTopLevelScope
    , moduleName
    , moduleNameString
    , moduleUnit
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
    , gHC_INTERNAL_DATA_FOLDABLE
    , eqClassKey
    , eqClassName
    , ge_RDR
    , gt_RDR
    , fractionalClassKey
    , fractionalClassKeys
    , gHC_INTERNAL_REAL
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
    , liftedTypeKind
    , listTyCon
    , listTyConName
    , naturalTy
    , nilDataCon
    , stringTy
    , true_RDR
    , trueDataCon
    , trueDataConId
    , tupleDataCon
    , tupleTyCon
    , typeSymbolKind
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
    , cmpAlt
    , collectArgs
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
    )
import GHC.Core.Class                 as Ghc
    ( classAllSelIds
    , classBigSig
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
    ( coAxiomTyCon )
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
    , instEnvElts
    , instanceSig
    )
import GHC.Core.Make                  as Ghc
    ( mkCoreApps
    , mkCoreConApps
    , mkCoreLams
    , mkCoreLets
    , pAT_ERROR_ID
    )
import GHC.Core.Predicate             as Ghc (getClassPredTys_maybe, getClassPredTys, isEvVarType, isEqPrimPred, isEqPred, isClassPred, isDictId, mkClassPred)
import GHC.Core.Reduction             as Ghc
    ( Reduction(Reduction) )
import GHC.Core.Subst                 as Ghc (emptySubst, extendCvSubst)
import GHC.Core.TyCo.Rep              as Ghc
    ( FunTyFlag(FTF_T_T, FTF_C_T)
    , ForAllTyFlag(Required)
    , Coercion (AxiomInstCo, SymCo)
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
import GHC.Core.TyCo.Subst            as Ghc (extendSubstInScopeSet, substCo, zipTvSubst)
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
    ( ruleMatchTyKiX, tcUnifyTy )
import GHC.Core.Utils                 as Ghc (exprType)
import GHC.Data.Bag                   as Ghc
    ( Bag, bagToList )
import GHC.Data.FastString            as Ghc
    ( FastString
    , bytesFS
    , concatFS
    , fsLit
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
    )
import GHC.Driver.Phases              as Ghc (Phase(StopLn))
import GHC.Driver.Pipeline            as Ghc (compileFile)
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
    ( IfaceAnnotation(ifAnnotatedValue) )
import GHC.Plugins                    as Ghc ( deserializeWithData
                                             , fromSerialized
                                             , toSerialized
                                             , defaultPlugin
                                             , emptyPlugins
                                             , Plugin(..)
                                             , CommandLineOption
                                             , purePlugin
                                             , extendIdSubst
                                             , substExpr
                                             )
import GHC.Core.FVs                   as Ghc (exprFreeVars, exprFreeVarsList, exprSomeFreeVarsList)
import GHC.Core.Opt.OccurAnal         as Ghc
    ( occurAnalysePgm )
import GHC.Core.TyCo.FVs              as Ghc (tyCoVarsOfCo, tyCoVarsOfType)
import GHC.Driver.Backend             as Ghc (interpreterBackend)
import GHC.Driver.Env                 as Ghc
    ( HscEnv(hsc_mod_graph, hsc_unit_env, hsc_dflags, hsc_plugins)
    , Hsc
    , hscSetFlags, hscUpdateFlags
    )
import GHC.Driver.Main                as Ghc
    ( hscDesugar )
import GHC.Driver.Errors              as Ghc
    ( printMessages )
import GHC.Driver.Ppr                 as Ghc
    ( showPpr
    , showSDoc
    )
import GHC.Hs                         as Ghc
    ( HsParsedModule(..)
    )
import GHC.HsToCore.Expr              as Ghc
    ( dsLExpr )
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
import GHC.Tc.Gen.App                 as Ghc (tcInferSigma)
import GHC.Tc.Gen.Bind                as Ghc (tcValBinds)
import GHC.Tc.Gen.Expr                as Ghc (tcInferRho)
import GHC.Tc.Solver                  as Ghc
    ( InferMode(NoRestrictions)
    , captureTopConstraints
    , simplifyInfer
    , simplifyInteractive
    )
import GHC.Tc.Types                   as Ghc
    ( Env(env_top)
    , TcGblEnv(tcg_anns, tcg_exports, tcg_insts, tcg_mod, tcg_rdr_env, tcg_rn_imports)
    , TcM
    , TcRn
    )
import GHC.Tc.Types.Evidence          as Ghc
    ( TcEvBinds(EvBinds) )
import GHC.Tc.Types.Origin            as Ghc (lexprCtOrigin)
import GHC.Tc.Utils.Monad             as Ghc
    ( captureConstraints
    , discardConstraints
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
    )
import GHC.Types.Basic                as Ghc
    ( Arity
    , Boxity(Boxed)
    , PprPrec
    , PromotionFlag(NotPromoted)
    , TopLevelFlag(NotTopLevel)
    , funPrec
    , InlinePragma(inl_act, inl_inline, inl_rule, inl_sat, inl_src)
    , isDeadOcc
    , isNoInlinePragma
    , isStrongLoopBreaker
    , noOccInfo
    , topPrec
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
    , idInlinePragma
    , modifyIdInfo
    , mkExportedLocalId
    , mkUserLocalOrCoVar
    , realIdUnfolding
    , setIdInfo
    )
import GHC.Types.Id.Info              as Ghc
    ( CafInfo(NoCafRefs)
    , IdDetails(DataConWorkId, DataConWrapId, RecSelId, VanillaId)
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
    , Literal(LitChar, LitDouble, LitFloat, LitNumber, LitString)
    , literalType
    )
import GHC.Types.Name                 as Ghc
    ( OccName
    , getOccString
    , getSrcSpan
    , isInternalName
    , isSystemName
    , mkInternalName
    , mkSystemName
    , mkTcOcc
    , mkTyVarOcc
    , mkVarOcc
    , mkVarOccFS
    , nameModule_maybe
    , nameOccName
    , nameSrcLoc
    , nameStableString
    , occNameFS
    , occNameString
    , stableNameCmp
    )
import GHC.Types.Name.Reader          as Ghc
    ( ImpItemSpec(ImpAll)
    , getRdrName
    , globalRdrEnvElts
    , greName
    , mkQual
    , mkVarUnqual
    , mkUnqual
    , nameRdrName
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
    , mkGeneralSrcSpan
    , mkRealSrcLoc
    , mkRealSrcSpan
    , realSrcSpanStart
    , srcSpanFileName_maybe
    , srcSpanToRealSrcSpan
    )
import GHC.Types.Tickish              as Ghc (CoreTickish, GenTickish(..))
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
    ( emptyInScopeSet, mkRnEnv2 )
import GHC.Types.Var.Set              as Ghc
    ( VarSet
    , elemVarSet
    , emptyVarSet
    , extendVarSet
    , extendVarSetList
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
    )
import GHC.Unit.Home.ModInfo          as Ghc
    ( HomePackageTable, HomeModInfo(hm_iface), lookupHpt )
import GHC.Unit.Module                as Ghc
    ( GenWithIsBoot(gwib_isBoot, gwib_mod)
    , IsBootInterface(NotBoot, IsBoot)
    , ModuleNameWithIsBoot
    , UnitId
    , fsToUnit
    , mkModuleNameFS
    , moduleNameFS
    , moduleStableString
    , toUnitId
    , unitString
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
import GHC.Utils.Error                as Ghc (pprLocMsgEnvelope, withTiming)
import GHC.Utils.Logger               as Ghc (Logger(logFlags), putLogMsg)
import GHC.Utils.Outputable           as Ghc hiding ((<>))
import GHC.Utils.Panic                as Ghc (panic, throwGhcException, throwGhcExceptionIO)
import GHC.Utils.Misc                 as Ghc (lengthAtLeast)
