{-
(c) The University of Glasgow 2006
(c) The GRASP/AQUA Project, Glasgow University, 1992-1998


Pattern-matching bindings (HsBinds and MonoBinds)

Handles @HsBinds@; those at the top level require different handling,
in that the @Rec@/@NonRec@/etc structure is thrown away (whereas at
lower levels it is preserved with @let@/@letrec@s).
-}

{-# LANGUAGE CPP #-}

module Language.Haskell.Liquid.Desugar.DsBinds ( dsTopLHsBinds, dsLHsBinds, decomposeRuleLhs, dsSpec,
                 dsHsWrapper, dsTcEvBinds, dsTcEvBinds_s, dsEvBinds, dsMkUserRule
  ) where

import {-# SOURCE #-}   Language.Haskell.Liquid.Desugar.DsExpr( dsLExpr )
import {-# SOURCE #-}   Language.Haskell.Liquid.Desugar.Match( matchWrapper )

import Language.Haskell.Liquid.Desugar.DsMonad
import Language.Haskell.Liquid.Desugar.DsGRHSs
import Language.Haskell.Liquid.Desugar.DsUtils

import HsSyn            -- lots of things
import CoreSyn          -- lots of things
import Literal          ( Literal(MachStr) )
import CoreSubst
import OccurAnal        ( occurAnalyseExpr )
import MkCore
import CoreUtils
import CoreArity ( etaExpand )
import CoreUnfold
import CoreFVs
import Digraph

import PrelNames
import TysPrim ( mkProxyPrimTy )
import TyCon
import TcEvidence
import TcType
import Type
import Coercion
import TysWiredIn ( typeNatKind, typeSymbolKind )
import Id
import MkId(proxyHashId)
import Class
import Name
import VarSet
import Rules
import VarEnv
import Outputable
import Module
import SrcLoc
import Maybes
import OrdList
import Bag
import BasicTypes hiding ( TopLevel )
import DynFlags
import FastString
import Util
import MonadUtils
import qualified GHC.LanguageExtensions as LangExt
import Control.Monad

{-**********************************************************************
*                                                                      *
           Desugaring a MonoBinds
*                                                                      *
**********************************************************************-}

-- | Desugar top level binds, strict binds are treated like normal
-- binds since there is no good time to force before first usage.
dsTopLHsBinds :: LHsBinds Id -> DsM (OrdList (Id,CoreExpr))
dsTopLHsBinds binds = fmap (toOL . snd) (ds_lhs_binds binds)

-- | Desugar all other kind of bindings, Ids of strict binds are returned to
-- later be forced in the binding gorup body, see Note [Desugar Strict binds]
dsLHsBinds :: LHsBinds Id
           -> DsM ([Id], [(Id,CoreExpr)])
dsLHsBinds binds = do { (force_vars, binds') <- ds_lhs_binds binds
                      ; return (force_vars, binds') }

------------------------

ds_lhs_binds :: LHsBinds Id -> DsM ([Id], [(Id,CoreExpr)])

ds_lhs_binds binds
  = do { ds_bs <- mapBagM dsLHsBind binds
       ; return (foldBag (\(a, a') (b, b') -> (a ++ b, a' ++ b'))
                         id ([], []) ds_bs) }

dsLHsBind :: LHsBind Id
          -> DsM ([Id], [(Id,CoreExpr)])
dsLHsBind (L loc bind) = do dflags <- getDynFlags
                            putSrcSpanDs loc $ dsHsBind dflags bind

-- | Desugar a single binding (or group of recursive binds).
dsHsBind :: DynFlags
         -> HsBind Id
         -> DsM ([Id], [(Id,CoreExpr)])
         -- ^ The Ids of strict binds, to be forced in the body of the
         -- binding group see Note [Desugar Strict binds] and all
         -- bindings and their desugared right hand sides.

dsHsBind dflags
         (VarBind { var_id = var
                  , var_rhs = expr
                  , var_inline = inline_regardless })
  = do  { core_expr <- dsLExpr expr
                -- Dictionary bindings are always VarBinds,
                -- so we only need do this here
        ; let var' | inline_regardless = var `setIdUnfolding` mkCompulsoryUnfolding core_expr
                   | otherwise         = var
        ; let core_bind@(id,_) = makeCorePair dflags var' False 0 core_expr
              force_var = if xopt LangExt.Strict dflags
                          then [id]
                          else []
        ; return (force_var, [core_bind]) }

dsHsBind dflags
         (FunBind { fun_id = L _ fun, fun_matches = matches
                  , fun_co_fn = co_fn, fun_tick = tick })
 = do   { (args, body) <- matchWrapper (FunRhs (idName fun)) Nothing matches
        ; let body' = mkOptTickBox tick body
        ; rhs <- dsHsWrapper co_fn (mkLams args body')
        ; let core_binds@(id,_) = makeCorePair dflags fun False 0 rhs
              force_var =
                if xopt LangExt.Strict dflags
                   && matchGroupArity matches == 0 -- no need to force lambdas
                then [id]
                else []
        ; {- pprTrace "dsHsBind" (ppr fun <+> ppr (idInlinePragma fun)) $ -}
           return (force_var, [core_binds]) }

dsHsBind dflags
         (PatBind { pat_lhs = pat, pat_rhs = grhss, pat_rhs_ty = ty
                  , pat_ticks = (rhs_tick, var_ticks) })
  = do  { body_expr <- dsGuarded grhss ty
        ; let body' = mkOptTickBox rhs_tick body_expr
              pat'  = decideBangHood dflags pat
        ; (force_var,sel_binds) <- mkSelectorBinds var_ticks pat body'
          -- We silently ignore inline pragmas; no makeCorePair
          -- Not so cool, but really doesn't matter
        ; let force_var' = if isBangedLPat pat'
                           then [force_var]
                           else []
        ; return (force_var', sel_binds) }

        -- A common case: one exported variable, only non-strict binds
        -- Non-recursive bindings come through this way
        -- So do self-recursive bindings
        -- Bindings with complete signatures are AbsBindsSigs, below
dsHsBind dflags
         (AbsBinds { abs_tvs = tyvars, abs_ev_vars = dicts
                   , abs_exports = [export]
                   , abs_ev_binds = ev_binds, abs_binds = binds })
  | ABE { abe_wrap = wrap, abe_poly = global
        , abe_mono = local, abe_prags = prags } <- export
  , not (xopt LangExt.Strict dflags)             -- Handle strict binds
  , not (anyBag (isBangedPatBind . unLoc) binds) --        in the next case
  = -- See Note [AbsBinds wrappers] in HsBinds
    addDictsDs (toTcTypeBag (listToBag dicts)) $
         -- addDictsDs: push type constraints deeper for pattern match check
    do { (_, bind_prs) <- ds_lhs_binds binds
       ; let core_bind = Rec bind_prs
       ; ds_binds <- dsTcEvBinds_s ev_binds
       ; rhs <- dsHsWrapper wrap $  -- Usually the identity
                mkLams tyvars $ mkLams dicts $
                mkCoreLets ds_binds $
                Let core_bind $
                Var local

       ; (spec_binds, rules) <- dsSpecs rhs prags

       ; let   global'  = addIdSpecialisations global rules
               main_bind = makeCorePair dflags global' (isDefaultMethod prags)
                                        (dictArity dicts) rhs

       ; return ([], main_bind : fromOL spec_binds) }

dsHsBind dflags
         (AbsBinds { abs_tvs = tyvars, abs_ev_vars = dicts
                   , abs_exports = exports, abs_ev_binds = ev_binds
                   , abs_binds = binds })
         -- See Note [Desugaring AbsBinds]
  = addDictsDs (toTcTypeBag (listToBag dicts)) $
         -- addDictsDs: push type constraints deeper for pattern match check
     do { (local_force_vars, bind_prs) <- ds_lhs_binds binds
        ; let core_bind = Rec [ makeCorePair dflags (add_inline lcl_id) False 0 rhs
                              | (lcl_id, rhs) <- bind_prs ]
                -- Monomorphic recursion possible, hence Rec
              new_force_vars = get_new_force_vars local_force_vars
              locals       = map abe_mono exports
              all_locals   = locals ++ new_force_vars
              tup_expr     = mkBigCoreVarTup all_locals
              tup_ty       = exprType tup_expr
        ; ds_binds <- dsTcEvBinds_s ev_binds
        ; let poly_tup_rhs = mkLams tyvars $ mkLams dicts $
                             mkCoreLets ds_binds $
                             Let core_bind $
                             tup_expr

        ; poly_tup_id <- newSysLocalDs (exprType poly_tup_rhs)

        -- Find corresponding global or make up a new one: sometimes
        -- we need to make new export to desugar strict binds, see
        -- Note [Desugar Strict binds]
        ; (exported_force_vars, extra_exports) <- get_exports local_force_vars

        ; let mk_bind (ABE { abe_wrap = wrap
                           , abe_poly = global
                           , abe_mono = local, abe_prags = spec_prags })
                         -- See Note [AbsBinds wrappers] in HsBinds
                = do { tup_id  <- newSysLocalDs tup_ty
                     ; rhs <- dsHsWrapper wrap $
                              mkLams tyvars $ mkLams dicts $
                              mkTupleSelector all_locals local tup_id $
                              mkVarApps (Var poly_tup_id) (tyvars ++ dicts)
                     ; let rhs_for_spec = Let (NonRec poly_tup_id poly_tup_rhs) rhs
                     ; (spec_binds, rules) <- dsSpecs rhs_for_spec spec_prags
                     ; let global' = (global `setInlinePragma` defaultInlinePragma)
                                             `addIdSpecialisations` rules
                           -- Kill the INLINE pragma because it applies to
                           -- the user written (local) function.  The global
                           -- Id is just the selector.  Hmm.
                     ; return ((global', rhs) : fromOL spec_binds) }

        ; export_binds_s <- mapM mk_bind (exports ++ extra_exports)

        ; return (exported_force_vars
                 ,(poly_tup_id, poly_tup_rhs) :
                   concat export_binds_s) }
  where
    inline_env :: IdEnv Id   -- Maps a monomorphic local Id to one with
                             -- the inline pragma from the source
                             -- The type checker put the inline pragma
                             -- on the *global* Id, so we need to transfer it
    inline_env
      = mkVarEnv [ (lcl_id, setInlinePragma lcl_id prag)
                 | ABE { abe_mono = lcl_id, abe_poly = gbl_id } <- exports
                 , let prag = idInlinePragma gbl_id ]

    add_inline :: Id -> Id    -- tran
    add_inline lcl_id = lookupVarEnv inline_env lcl_id
                        `orElse` lcl_id

    global_env :: IdEnv Id -- Maps local Id to its global exported Id
    global_env =
      mkVarEnv [ (local, global)
               | ABE { abe_mono = local, abe_poly = global } <- exports
               ]

    -- find variables that are not exported
    get_new_force_vars lcls =
      foldr (\lcl acc -> case lookupVarEnv global_env lcl of
                           Just _ -> acc
                           Nothing -> lcl:acc)
            [] lcls

    -- find exports or make up new exports for force variables
    get_exports :: [Id] -> DsM ([Id], [ABExport Id])
    get_exports lcls =
      foldM (\(glbls, exports) lcl ->
              case lookupVarEnv global_env lcl of
                Just glbl -> return (glbl:glbls, exports)
                Nothing   -> do export <- mk_export lcl
                                let glbl = abe_poly export
                                return (glbl:glbls, export:exports))
            ([],[]) lcls

    mk_export local =
      do global <- newSysLocalDs
                     (exprType (mkLams tyvars (mkLams dicts (Var local))))
         return (ABE {abe_poly = global
                     ,abe_mono = local
                     ,abe_wrap = WpHole
                     ,abe_prags = SpecPrags []})

-- AbsBindsSig is a combination of AbsBinds and FunBind
dsHsBind dflags (AbsBindsSig { abs_tvs = tyvars, abs_ev_vars = dicts
                             , abs_sig_export  = global
                             , abs_sig_prags   = prags
                             , abs_sig_ev_bind = ev_bind
                             , abs_sig_bind    = bind })
  | L bind_loc FunBind { fun_matches = matches
                       , fun_co_fn   = co_fn
                       , fun_tick    = tick } <- bind
  = putSrcSpanDs bind_loc $
    addDictsDs (toTcTypeBag (listToBag dicts)) $
             -- addDictsDs: push type constraints deeper for pattern match check
    do { (args, body) <- matchWrapper (FunRhs (idName global)) Nothing matches
       ; let body' = mkOptTickBox tick body
       ; fun_rhs <- dsHsWrapper co_fn $
                    mkLams args body'
       ; let force_vars
               | xopt LangExt.Strict dflags
               , matchGroupArity matches == 0 -- no need to force lambdas
               = [global]
               | otherwise
               = []

       ; ds_binds <- dsTcEvBinds ev_bind
       ; let rhs = mkLams tyvars $
                   mkLams dicts $
                   mkCoreLets ds_binds $
                   fun_rhs

       ; (spec_binds, rules) <- dsSpecs rhs prags
       ; let global' = addIdSpecialisations global rules
             main_bind = makeCorePair dflags global' (isDefaultMethod prags)
                                      (dictArity dicts) rhs

       ; return (force_vars, main_bind : fromOL spec_binds) }

  | otherwise
  = pprPanic "dsHsBind: AbsBindsSig" (ppr bind)

dsHsBind _ (PatSynBind{}) = panic "dsHsBind: PatSynBind"


------------------------
makeCorePair :: DynFlags -> Id -> Bool -> Arity -> CoreExpr -> (Id, CoreExpr)
makeCorePair dflags gbl_id is_default_method dict_arity rhs
  | is_default_method                 -- Default methods are *always* inlined
  = (gbl_id `setIdUnfolding` mkCompulsoryUnfolding rhs, rhs)

  | otherwise
  = case inlinePragmaSpec inline_prag of
          EmptyInlineSpec -> (gbl_id, rhs)
          NoInline        -> (gbl_id, rhs)
          Inlinable       -> (gbl_id `setIdUnfolding` inlinable_unf, rhs)
          Inline          -> inline_pair

  where
    inline_prag   = idInlinePragma gbl_id
    inlinable_unf = mkInlinableUnfolding dflags rhs
    inline_pair
       | Just arity <- inlinePragmaSat inline_prag
        -- Add an Unfolding for an INLINE (but not for NOINLINE)
        -- And eta-expand the RHS; see Note [Eta-expanding INLINE things]
       , let real_arity = dict_arity + arity
        -- NB: The arity in the InlineRule takes account of the dictionaries
       = ( gbl_id `setIdUnfolding` mkInlineUnfolding (Just real_arity) rhs
         , etaExpand real_arity rhs)

       | otherwise
       = pprTrace "makeCorePair: arity missing" (ppr gbl_id) $
         (gbl_id `setIdUnfolding` mkInlineUnfolding Nothing rhs, rhs)

dictArity :: [Var] -> Arity
-- Don't count coercion variables in arity
dictArity dicts = count isId dicts

{-
Note [Desugaring AbsBinds]
~~~~~~~~~~~~~~~~~~~~~~~~~~
In the general AbsBinds case we desugar the binding to this:

       tup a (d:Num a) = let fm = ...gm...
                             gm = ...fm...
                         in (fm,gm)
       f a d = case tup a d of { (fm,gm) -> fm }
       g a d = case tup a d of { (fm,gm) -> fm }

Note [Rules and inlining]
~~~~~~~~~~~~~~~~~~~~~~~~~
Common special case: no type or dictionary abstraction
This is a bit less trivial than you might suppose
The naive way woudl be to desguar to something like
        f_lcl = ...f_lcl...     -- The "binds" from AbsBinds
        M.f = f_lcl             -- Generated from "exports"
But we don't want that, because if M.f isn't exported,
it'll be inlined unconditionally at every call site (its rhs is
trivial).  That would be ok unless it has RULES, which would
thereby be completely lost.  Bad, bad, bad.

Instead we want to generate
        M.f = ...f_lcl...
        f_lcl = M.f
Now all is cool. The RULES are attached to M.f (by SimplCore),
and f_lcl is rapidly inlined away.

This does not happen in the same way to polymorphic binds,
because they desugar to
        M.f = /\a. let f_lcl = ...f_lcl... in f_lcl
Although I'm a bit worried about whether full laziness might
float the f_lcl binding out and then inline M.f at its call site

Note [Specialising in no-dict case]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Even if there are no tyvars or dicts, we may have specialisation pragmas.
Class methods can generate
      AbsBinds [] [] [( ... spec-prag]
         { AbsBinds [tvs] [dicts] ...blah }
So the overloading is in the nested AbsBinds. A good example is in GHC.Float:

  class  (Real a, Fractional a) => RealFrac a  where
    round :: (Integral b) => a -> b

  instance  RealFrac Float  where
    {-# SPECIALIZE round :: Float -> Int #-}

The top-level AbsBinds for $cround has no tyvars or dicts (because the
instance does not).  But the method is locally overloaded!

Note [Abstracting over tyvars only]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
When abstracting over type variable only (not dictionaries), we don't really need to
built a tuple and select from it, as we do in the general case. Instead we can take

        AbsBinds [a,b] [ ([a,b], fg, fl, _),
                         ([b],   gg, gl, _) ]
                { fl = e1
                  gl = e2
                   h = e3 }

and desugar it to

        fg = /\ab. let B in e1
        gg = /\b. let a = () in let B in S(e2)
        h  = /\ab. let B in e3

where B is the *non-recursive* binding
        fl = fg a b
        gl = gg b
        h  = h a b    -- See (b); note shadowing!

Notice (a) g has a different number of type variables to f, so we must
             use the mkArbitraryType thing to fill in the gaps.
             We use a type-let to do that.

         (b) The local variable h isn't in the exports, and rather than
             clone a fresh copy we simply replace h by (h a b), where
             the two h's have different types!  Shadowing happens here,
             which looks confusing but works fine.

         (c) The result is *still* quadratic-sized if there are a lot of
             small bindings.  So if there are more than some small
             number (10), we filter the binding set B by the free
             variables of the particular RHS.  Tiresome.

Why got to this trouble?  It's a common case, and it removes the
quadratic-sized tuple desugaring.  Less clutter, hopefully faster
compilation, especially in a case where there are a *lot* of
bindings.


Note [Eta-expanding INLINE things]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider
   foo :: Eq a => a -> a
   {-# INLINE foo #-}
   foo x = ...

If (foo d) ever gets floated out as a common sub-expression (which can
happen as a result of method sharing), there's a danger that we never
get to do the inlining, which is a Terribly Bad thing given that the
user said "inline"!

To avoid this we pre-emptively eta-expand the definition, so that foo
has the arity with which it is declared in the source code.  In this
example it has arity 2 (one for the Eq and one for x). Doing this
should mean that (foo d) is a PAP and we don't share it.

Note [Nested arities]
~~~~~~~~~~~~~~~~~~~~~
For reasons that are not entirely clear, method bindings come out looking like
this:

  AbsBinds [] [] [$cfromT <= [] fromT]
    $cfromT [InlPrag=INLINE] :: T Bool -> Bool
    { AbsBinds [] [] [fromT <= [] fromT_1]
        fromT :: T Bool -> Bool
        { fromT_1 ((TBool b)) = not b } } }

Note the nested AbsBind.  The arity for the InlineRule on $cfromT should be
gotten from the binding for fromT_1.

It might be better to have just one level of AbsBinds, but that requires more
thought!


Note [Desugar Strict binds]
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Desugaring strict variable bindings looks as follows (core below ==>)

  let !x = rhs
  in  body
==>
  let x = rhs
  in x `seq` body -- seq the variable

and if it is a pattern binding the desugaring looks like

  let !pat = rhs
  in body
==>
  let x = rhs -- bind the rhs to a new variable
      pat = x
  in x `seq` body -- seq the new variable

if there is no variable in the pattern desugaring looks like

  let False = rhs
  in body
==>
  let x = case rhs of {False -> (); _ -> error "Match failed"}
  in x `seq` body

In order to force the Ids in the binding group they are passed around
in the dsHsBind family of functions, and later seq'ed in DsExpr.ds_val_bind.

Consider a recursive group like this

  letrec
     f : g = rhs[f,g]
  in <body>

Without `Strict`, we get a translation like this:

  let t = /\a. letrec tm = rhs[fm,gm]
                      fm = case t of fm:_ -> fm
                      gm = case t of _:gm -> gm
                in
                (fm,gm)

  in let f = /\a. case t a of (fm,_) -> fm
  in let g = /\a. case t a of (_,gm) -> gm
  in <body>

Here `tm` is the monomorphic binding for `rhs`.

With `Strict`, we want to force `tm`, but NOT `fm` or `gm`.
Alas, `tm` isn't in scope in the `in <body>` part.

The simplest thing is to return it in the polymorphic
tuple `t`, thus:

  let t = /\a. letrec tm = rhs[fm,gm]
                      fm = case t of fm:_ -> fm
                      gm = case t of _:gm -> gm
                in
                (tm, fm, gm)

  in let f = /\a. case t a of (_,fm,_) -> fm
  in let g = /\a. case t a of (_,_,gm) -> gm
  in let tm = /\a. case t a of (tm,_,_) -> tm
  in tm `seq` <body>


See https://ghc.haskell.org/trac/ghc/wiki/StrictPragma for a more
detailed explanation of the desugaring of strict bindings.

-}

------------------------
dsSpecs :: CoreExpr     -- Its rhs
        -> TcSpecPrags
        -> DsM ( OrdList (Id,CoreExpr)  -- Binding for specialised Ids
               , [CoreRule] )           -- Rules for the Global Ids
-- See Note [Handling SPECIALISE pragmas] in TcBinds
dsSpecs _ IsDefaultMethod = return (nilOL, [])
dsSpecs poly_rhs (SpecPrags sps)
  = do { pairs <- mapMaybeM (dsSpec (Just poly_rhs)) sps
       ; let (spec_binds_s, rules) = unzip pairs
       ; return (concatOL spec_binds_s, rules) }

dsSpec :: Maybe CoreExpr        -- Just rhs => RULE is for a local binding
                                -- Nothing => RULE is for an imported Id
                                --            rhs is in the Id's unfolding
       -> Located TcSpecPrag
       -> DsM (Maybe (OrdList (Id,CoreExpr), CoreRule))
dsSpec mb_poly_rhs (L loc (SpecPrag poly_id spec_co spec_inl))
  | isJust (isClassOpId_maybe poly_id)
  = putSrcSpanDs loc $
    do { warnDs NoReason (text "Ignoring useless SPECIALISE pragma for class method selector"
                          <+> quotes (ppr poly_id))
       ; return Nothing  }  -- There is no point in trying to specialise a class op
                            -- Moreover, classops don't (currently) have an inl_sat arity set
                            -- (it would be Just 0) and that in turn makes makeCorePair bleat

  | no_act_spec && isNeverActive rule_act
  = putSrcSpanDs loc $
    do { warnDs NoReason (text "Ignoring useless SPECIALISE pragma for NOINLINE function:"
                          <+> quotes (ppr poly_id))
       ; return Nothing  }  -- Function is NOINLINE, and the specialiation inherits that
                            -- See Note [Activation pragmas for SPECIALISE]

  | otherwise
  = putSrcSpanDs loc $
    do { uniq <- newUnique
       ; let poly_name = idName poly_id
             spec_occ  = mkSpecOcc (getOccName poly_name)
             spec_name = mkInternalName uniq spec_occ (getSrcSpan poly_name)
       ; (bndrs, ds_lhs) <- liftM collectBinders
                                  (dsHsWrapper spec_co (Var poly_id))
       ; let spec_ty = mkPiTypes bndrs (exprType ds_lhs)
       ; -- pprTrace "dsRule" (vcat [ text "Id:" <+> ppr poly_id
         --                         , text "spec_co:" <+> ppr spec_co
         --                         , text "ds_rhs:" <+> ppr ds_lhs ]) $
         case decomposeRuleLhs bndrs ds_lhs of {
           Left msg -> do { warnDs NoReason msg; return Nothing } ;
           Right (rule_bndrs, _fn, args) -> do

       { dflags <- getDynFlags
       ; this_mod <- getModule
       ; let fn_unf    = realIdUnfolding poly_id
             unf_fvs   = stableUnfoldingVars fn_unf `orElse` emptyVarSet
             in_scope  = mkInScopeSet (unf_fvs `unionVarSet` exprsFreeVars args)
             spec_unf  = specUnfolding dflags (mkEmptySubst in_scope) bndrs args fn_unf
             spec_id   = mkLocalId spec_name spec_ty
                            `setInlinePragma` inl_prag
                            `setIdUnfolding`  spec_unf
       ; rule <- dsMkUserRule this_mod is_local_id
                        (mkFastString ("SPEC " ++ showPpr dflags poly_name))
                        rule_act poly_name
                        rule_bndrs args
                        (mkVarApps (Var spec_id) bndrs)

       ; spec_rhs <- dsHsWrapper spec_co poly_rhs

-- Commented out: see Note [SPECIALISE on INLINE functions]
--       ; when (isInlinePragma id_inl)
--              (warnDs $ text "SPECIALISE pragma on INLINE function probably won't fire:"
--                        <+> quotes (ppr poly_name))

       ; return (Just (unitOL (spec_id, spec_rhs), rule))
            -- NB: do *not* use makeCorePair on (spec_id,spec_rhs), because
            --     makeCorePair overwrites the unfolding, which we have
            --     just created using specUnfolding
       } } }
  where
    is_local_id = isJust mb_poly_rhs
    poly_rhs | Just rhs <-  mb_poly_rhs
             = rhs          -- Local Id; this is its rhs
             | Just unfolding <- maybeUnfoldingTemplate (realIdUnfolding poly_id)
             = unfolding    -- Imported Id; this is its unfolding
                            -- Use realIdUnfolding so we get the unfolding
                            -- even when it is a loop breaker.
                            -- We want to specialise recursive functions!
             | otherwise = pprPanic "dsImpSpecs" (ppr poly_id)
                            -- The type checker has checked that it *has* an unfolding

    id_inl = idInlinePragma poly_id

    -- See Note [Activation pragmas for SPECIALISE]
    inl_prag | not (isDefaultInlinePragma spec_inl)    = spec_inl
             | not is_local_id  -- See Note [Specialising imported functions]
                                 -- in OccurAnal
             , isStrongLoopBreaker (idOccInfo poly_id) = neverInlinePragma
             | otherwise                               = id_inl
     -- Get the INLINE pragma from SPECIALISE declaration, or,
     -- failing that, from the original Id

    spec_prag_act = inlinePragmaActivation spec_inl

    -- See Note [Activation pragmas for SPECIALISE]
    -- no_act_spec is True if the user didn't write an explicit
    -- phase specification in the SPECIALISE pragma
    no_act_spec = case inlinePragmaSpec spec_inl of
                    NoInline -> isNeverActive  spec_prag_act
                    _        -> isAlwaysActive spec_prag_act
    rule_act | no_act_spec = inlinePragmaActivation id_inl   -- Inherit
             | otherwise   = spec_prag_act                   -- Specified by user


dsMkUserRule :: Module -> Bool -> RuleName -> Activation
       -> Name -> [CoreBndr] -> [CoreExpr] -> CoreExpr -> DsM CoreRule
dsMkUserRule this_mod is_local name act fn bndrs args rhs = do
    let rule = mkRule this_mod False is_local name act fn bndrs args rhs
    dflags <- getDynFlags
    when (isOrphan (ru_orphan rule) && wopt Opt_WarnOrphans dflags) $
        warnDs (Reason Opt_WarnOrphans) (ruleOrphWarn rule)
    return rule

ruleOrphWarn :: CoreRule -> SDoc
ruleOrphWarn rule = text "Orphan rule:" <+> ppr rule

{- Note [SPECIALISE on INLINE functions]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We used to warn that using SPECIALISE for a function marked INLINE
would be a no-op; but it isn't!  Especially with worker/wrapper split
we might have
   {-# INLINE f #-}
   f :: Ord a => Int -> a -> ...
   f d x y = case x of I# x' -> $wf d x' y

We might want to specialise 'f' so that we in turn specialise '$wf'.
We can't even /name/ '$wf' in the source code, so we can't specialise
it even if we wanted to.  Trac #10721 is a case in point.

Note [Activation pragmas for SPECIALISE]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
From a user SPECIALISE pragma for f, we generate
  a) A top-level binding    spec_fn = rhs
  b) A RULE                 f dOrd = spec_fn

We need two pragma-like things:

* spec_fn's inline pragma: inherited from f's inline pragma (ignoring
                           activation on SPEC), unless overriden by SPEC INLINE

* Activation of RULE: from SPECIALISE pragma (if activation given)
                      otherwise from f's inline pragma

This is not obvious (see Trac #5237)!

Examples      Rule activation   Inline prag on spec'd fn
---------------------------------------------------------------------
SPEC [n] f :: ty            [n]   Always, or NOINLINE [n]
                                  copy f's prag

NOINLINE f
SPEC [n] f :: ty            [n]   NOINLINE
                                  copy f's prag

NOINLINE [k] f
SPEC [n] f :: ty            [n]   NOINLINE [k]
                                  copy f's prag

INLINE [k] f
SPEC [n] f :: ty            [n]   INLINE [k]
                                  copy f's prag

SPEC INLINE [n] f :: ty     [n]   INLINE [n]
                                  (ignore INLINE prag on f,
                                  same activation for rule and spec'd fn)

NOINLINE [k] f
SPEC f :: ty                [n]   INLINE [k]


************************************************************************
*                                                                      *
\subsection{Adding inline pragmas}
*                                                                      *
************************************************************************
-}

decomposeRuleLhs :: [Var] -> CoreExpr -> Either SDoc ([Var], Id, [CoreExpr])
-- (decomposeRuleLhs bndrs lhs) takes apart the LHS of a RULE,
-- The 'bndrs' are the quantified binders of the rules, but decomposeRuleLhs
-- may add some extra dictionary binders (see Note [Free dictionaries])
--
-- Returns Nothing if the LHS isn't of the expected shape
-- Note [Decomposing the left-hand side of a RULE]
decomposeRuleLhs orig_bndrs orig_lhs
  | not (null unbound)    -- Check for things unbound on LHS
                          -- See Note [Unused spec binders]
  = Left (vcat (map dead_msg unbound))

  | Just (fn_id, args) <- decompose fun2 args2
  , let extra_bndrs = mk_extra_bndrs fn_id args
  = -- pprTrace "decmposeRuleLhs" (vcat [ text "orig_bndrs:" <+> ppr orig_bndrs
    --                                  , text "orig_lhs:" <+> ppr orig_lhs
    --                                  , text "lhs1:"     <+> ppr lhs1
    --                                  , text "extra_dict_bndrs:" <+> ppr extra_dict_bndrs
    --                                  , text "fn_id:" <+> ppr fn_id
    --                                  , text "args:"   <+> ppr args]) $
    Right (orig_bndrs ++ extra_bndrs, fn_id, args)

  | otherwise
  = Left bad_shape_msg
 where
   lhs1         = drop_dicts orig_lhs
   lhs2         = simpleOptExpr lhs1  -- See Note [Simplify rule LHS]
   (fun2,args2) = collectArgs lhs2

   lhs_fvs    = exprFreeVars lhs2
   unbound    = filterOut (`elemVarSet` lhs_fvs) orig_bndrs

   orig_bndr_set = mkVarSet orig_bndrs

        -- Add extra tyvar binders: Note [Free tyvars in rule LHS]
        -- and extra dict binders: Note [Free dictionaries in rule LHS]
   mk_extra_bndrs fn_id args
     = toposortTyVars unbound_tvs ++ unbound_dicts
     where
       unbound_tvs   = [ v | v <- unbound_vars, isTyVar v ]
       unbound_dicts = [ mkLocalId (localiseName (idName d)) (idType d)
                       | d <- unbound_vars, isDictId d ]
       unbound_vars  = [ v | v <- exprsFreeVarsList args
                           , not (v `elemVarSet` orig_bndr_set)
                           , not (v == fn_id) ]
         -- fn_id: do not quantify over the function itself, which may
         -- itself be a dictionary (in pathological cases, Trac #10251)

   decompose (Var fn_id) args
      | not (fn_id `elemVarSet` orig_bndr_set)
      = Just (fn_id, args)

   decompose _ _ = Nothing

   bad_shape_msg = hang (text "RULE left-hand side too complicated to desugar")
                      2 (vcat [ text "Optimised lhs:" <+> ppr lhs2
                              , text "Orig lhs:" <+> ppr orig_lhs])
   dead_msg bndr = hang (sep [ text "Forall'd" <+> pp_bndr bndr
                             , text "is not bound in RULE lhs"])
                      2 (vcat [ text "Orig bndrs:" <+> ppr orig_bndrs
                              , text "Orig lhs:" <+> ppr orig_lhs
                              , text "optimised lhs:" <+> ppr lhs2 ])
   pp_bndr bndr
    | isTyVar bndr                      = text "type variable" <+> quotes (ppr bndr)
    | Just pred <- evVarPred_maybe bndr = text "constraint" <+> quotes (ppr pred)
    | otherwise                         = text "variable" <+> quotes (ppr bndr)

   drop_dicts :: CoreExpr -> CoreExpr
   drop_dicts e
       = wrap_lets needed bnds body
     where
       needed = orig_bndr_set `minusVarSet` exprFreeVars body
       (bnds, body) = split_lets (occurAnalyseExpr e)
           -- The occurAnalyseExpr drops dead bindings which is
           -- crucial to ensure that every binding is used later;
           -- which in turn makes wrap_lets work right

   split_lets :: CoreExpr -> ([(DictId,CoreExpr)], CoreExpr)
   split_lets (Let (NonRec d r) body)
     | isDictId d
     = ((d,r):bs, body')
     where (bs, body') = split_lets body

    -- handle "unlifted lets" too, needed for "map/coerce"
   split_lets (Case r d _ [(DEFAULT, _, body)])
     | isCoVar d
     = ((d,r):bs, body')
     where (bs, body') = split_lets body

   split_lets e = ([], e)

   wrap_lets :: VarSet -> [(DictId,CoreExpr)] -> CoreExpr -> CoreExpr
   wrap_lets _ [] body = body
   wrap_lets needed ((d, r) : bs) body
     | rhs_fvs `intersectsVarSet` needed = mkCoreLet (NonRec d r) (wrap_lets needed' bs body)
     | otherwise                         = wrap_lets needed bs body
     where
       rhs_fvs = exprFreeVars r
       needed' = (needed `minusVarSet` rhs_fvs) `extendVarSet` d

{-
Note [Decomposing the left-hand side of a RULE]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
There are several things going on here.
* drop_dicts: see Note [Drop dictionary bindings on rule LHS]
* simpleOptExpr: see Note [Simplify rule LHS]
* extra_dict_bndrs: see Note [Free dictionaries]

Note [Free tyvars on rule LHS]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider
  data T a = C

  foo :: T a -> Int
  foo C = 1

  {-# RULES "myrule"  foo C = 1 #-}

After type checking the LHS becomes (foo alpha (C alpha)), where alpha
is an unbound meta-tyvar.  The zonker in TcHsSyn is careful not to
turn the free alpha into Any (as it usually does).  Instead it turns it
into a skolem 'a'.  See TcHsSyn Note [Zonking the LHS of a RULE].

Now we must quantify over that 'a'.  It's /really/ inconvenient to do that
in the zonker, because the HsExpr data type is very large.  But it's /easy/
to do it here in the desugarer.

Moreover, we have to do something rather similar for dictionaries;
see Note [Free dictionaries on rule LHS].   So that's why we look for
type variables free on the LHS, and quantify over them.

Note [Free dictionaries on rule LHS]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
When the LHS of a specialisation rule, (/\as\ds. f es) has a free dict,
which is presumably in scope at the function definition site, we can quantify
over it too.  *Any* dict with that type will do.

So for example when you have
        f :: Eq a => a -> a
        f = <rhs>
        ... SPECIALISE f :: Int -> Int ...

Then we get the SpecPrag
        SpecPrag (f Int dInt)

And from that we want the rule

        RULE forall dInt. f Int dInt = f_spec
        f_spec = let f = <rhs> in f Int dInt

But be careful!  That dInt might be GHC.Base.$fOrdInt, which is an External
Name, and you can't bind them in a lambda or forall without getting things
confused.   Likewise it might have an InlineRule or something, which would be
utterly bogus. So we really make a fresh Id, with the same unique and type
as the old one, but with an Internal name and no IdInfo.

Note [Drop dictionary bindings on rule LHS]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
drop_dicts drops dictionary bindings on the LHS where possible.
   E.g.  let d:Eq [Int] = $fEqList $fEqInt in f d
     --> f d
   Reasoning here is that there is only one d:Eq [Int], and so we can
   quantify over it. That makes 'd' free in the LHS, but that is later
   picked up by extra_dict_bndrs (Note [Dead spec binders]).

   NB 1: We can only drop the binding if the RHS doesn't bind
         one of the orig_bndrs, which we assume occur on RHS.
         Example
            f :: (Eq a) => b -> a -> a
            {-# SPECIALISE f :: Eq a => b -> [a] -> [a] #-}
         Here we want to end up with
            RULE forall d:Eq a.  f ($dfEqList d) = f_spec d
         Of course, the ($dfEqlist d) in the pattern makes it less likely
         to match, but there is no other way to get d:Eq a

   NB 2: We do drop_dicts *before* simplOptEpxr, so that we expect all
         the evidence bindings to be wrapped around the outside of the
         LHS.  (After simplOptExpr they'll usually have been inlined.)
         dsHsWrapper does dependency analysis, so that civilised ones
         will be simple NonRec bindings.  We don't handle recursive
         dictionaries!

    NB3: In the common case of a non-overloaded, but perhaps-polymorphic
         specialisation, we don't need to bind *any* dictionaries for use
         in the RHS. For example (Trac #8331)
             {-# SPECIALIZE INLINE useAbstractMonad :: ReaderST s Int #-}
             useAbstractMonad :: MonadAbstractIOST m => m Int
         Here, deriving (MonadAbstractIOST (ReaderST s)) is a lot of code
         but the RHS uses no dictionaries, so we want to end up with
             RULE forall s (d :: MonadAbstractIOST (ReaderT s)).
                useAbstractMonad (ReaderT s) d = $suseAbstractMonad s

   Trac #8848 is a good example of where there are some intersting
   dictionary bindings to discard.

The drop_dicts algorithm is based on these observations:

  * Given (let d = rhs in e) where d is a DictId,
    matching 'e' will bind e's free variables.

  * So we want to keep the binding if one of the needed variables (for
    which we need a binding) is in fv(rhs) but not already in fv(e).

  * The "needed variables" are simply the orig_bndrs.  Consider
       f :: (Eq a, Show b) => a -> b -> String
       ... SPECIALISE f :: (Show b) => Int -> b -> String ...
    Then orig_bndrs includes the *quantified* dictionaries of the type
    namely (dsb::Show b), but not the one for Eq Int

So we work inside out, applying the above criterion at each step.


Note [Simplify rule LHS]
~~~~~~~~~~~~~~~~~~~~~~~~
simplOptExpr occurrence-analyses and simplifies the LHS:

   (a) Inline any remaining dictionary bindings (which hopefully
       occur just once)

   (b) Substitute trivial lets so that they don't get in the way
       Note that we substitute the function too; we might
       have this as a LHS:  let f71 = M.f Int in f71

   (c) Do eta reduction.  To see why, consider the fold/build rule,
       which without simplification looked like:
          fold k z (build (/\a. g a))  ==>  ...
       This doesn't match unless you do eta reduction on the build argument.
       Similarly for a LHS like
         augment g (build h)
       we do not want to get
         augment (\a. g a) (build h)
       otherwise we don't match when given an argument like
          augment (\a. h a a) (build h)

Note [Matching seqId]
~~~~~~~~~~~~~~~~~~~
The desugarer turns (seq e r) into (case e of _ -> r), via a special-case hack
and this code turns it back into an application of seq!
See Note [Rules for seq] in MkId for the details.

Note [Unused spec binders]
~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider
        f :: a -> a
        ... SPECIALISE f :: Eq a => a -> a ...
It's true that this *is* a more specialised type, but the rule
we get is something like this:
        f_spec d = f
        RULE: f = f_spec d
Note that the rule is bogus, because it mentions a 'd' that is
not bound on the LHS!  But it's a silly specialisation anyway, because
the constraint is unused.  We could bind 'd' to (error "unused")
but it seems better to reject the program because it's almost certainly
a mistake.  That's what the isDeadBinder call detects.

************************************************************************
*                                                                      *
                Desugaring evidence
*                                                                      *
************************************************************************

-}

dsHsWrapper :: HsWrapper -> CoreExpr -> DsM CoreExpr
dsHsWrapper WpHole            e = return e
dsHsWrapper (WpTyApp ty)      e = return $ App e (Type ty)
dsHsWrapper (WpLet ev_binds)  e = do bs <- dsTcEvBinds ev_binds
                                     return (mkCoreLets bs e)
dsHsWrapper (WpCompose c1 c2) e = do { e1 <- dsHsWrapper c2 e
                                     ; dsHsWrapper c1 e1 }
dsHsWrapper (WpFun c1 c2 t1)  e = do { x <- newSysLocalDs t1
                                     ; e1 <- dsHsWrapper c1 (Var x)
                                     ; e2 <- dsHsWrapper c2 (mkCoreAppDs (text "dsHsWrapper") e e1)
                                     ; return (Lam x e2) }
dsHsWrapper (WpCast co)       e = return $ mkCastDs e co
dsHsWrapper (WpEvLam ev)      e = return $ Lam ev e
dsHsWrapper (WpTyLam tv)      e = return $ Lam tv e
dsHsWrapper (WpEvApp    tm)   e = liftM (App e) (dsEvTerm tm)

--------------------------------------
dsTcEvBinds_s :: [TcEvBinds] -> DsM [CoreBind]
dsTcEvBinds_s []       = return []
dsTcEvBinds_s (b:_)    = dsTcEvBinds b

dsTcEvBinds :: TcEvBinds -> DsM [CoreBind]
dsTcEvBinds (TcEvBinds {}) = panic "dsEvBinds"    -- Zonker has got rid of this
dsTcEvBinds (EvBinds bs)   = dsEvBinds bs

dsEvBinds :: Bag EvBind -> DsM [CoreBind]
dsEvBinds bs = mapM ds_scc (sccEvBinds bs)
  where
    ds_scc (AcyclicSCC (EvBind { eb_lhs = v, eb_rhs = r}))
                          = liftM (NonRec v) (dsEvTerm r)
    ds_scc (CyclicSCC bs) = liftM Rec (mapM dsEvBind bs)

dsEvBind :: EvBind -> DsM (Id, CoreExpr)
dsEvBind (EvBind { eb_lhs = v, eb_rhs = r}) = liftM ((,) v) (dsEvTerm r)

{-**********************************************************************
*                                                                      *
           Desugaring EvTerms
*                                                                      *
**********************************************************************-}

dsEvTerm :: EvTerm -> DsM CoreExpr
dsEvTerm (EvId v)           = return (Var v)
dsEvTerm (EvCallStack cs)   = dsEvCallStack cs
dsEvTerm (EvTypeable ty ev) = dsEvTypeable ty ev
dsEvTerm (EvLit (EvNum n))  = mkIntegerExpr n
dsEvTerm (EvLit (EvStr s))  = mkStringExprFS s

dsEvTerm (EvCast tm co)
  = do { tm' <- dsEvTerm tm
       ; return $ mkCastDs tm' co }

dsEvTerm (EvDFunApp df tys tms)
  = do { tms' <- mapM dsEvTerm tms
       ; return $ Var df `mkTyApps` tys `mkApps` tms' }

dsEvTerm (EvCoercion co) = return (Coercion co)
dsEvTerm (EvSuperClass d n)
  = do { d' <- dsEvTerm d
       ; let (cls, tys) = getClassPredTys (exprType d')
             sc_sel_id  = classSCSelId cls n    -- Zero-indexed
       ; return $ Var sc_sel_id `mkTyApps` tys `App` d' }

dsEvTerm (EvDelayedError ty msg) = return $ dsEvDelayedError ty msg

dsEvDelayedError :: Type -> FastString -> CoreExpr
dsEvDelayedError ty msg
  = Var errorId `mkTyApps` [getRuntimeRep "dsEvTerm" ty, ty] `mkApps` [litMsg]
  where
    errorId = tYPE_ERROR_ID
    litMsg  = Lit (MachStr (fastStringToByteString msg))

{-**********************************************************************
*                                                                      *
           Desugaring Typeable dictionaries
*                                                                      *
**********************************************************************-}

dsEvTypeable :: Type -> EvTypeable -> DsM CoreExpr
-- Return a CoreExpr :: Typeable ty
-- This code is tightly coupled to the representation
-- of TypeRep, in base library Data.Typeable.Internals
dsEvTypeable ty ev
  = do { tyCl <- dsLookupTyCon typeableClassName   -- Typeable
       ; let kind = typeKind ty
             Just typeable_data_con
                 = tyConSingleDataCon_maybe tyCl      -- "Data constructor"
                                                      -- for Typeable

       ; rep_expr <- ds_ev_typeable ty ev

       -- Build Core for (let r::TypeRep = rep in \proxy. rep)
       -- See Note [Memoising typeOf]
       ; repName <- newSysLocalDs (exprType rep_expr)
       ; let proxyT = mkProxyPrimTy kind ty
             method = bindNonRec repName rep_expr
                      $ mkLams [mkWildValBinder proxyT] (Var repName)

       -- Package up the method as `Typeable` dictionary
       ; return $ mkConApp typeable_data_con [Type kind, Type ty, method] }


ds_ev_typeable :: Type -> EvTypeable -> DsM CoreExpr
-- Returns a CoreExpr :: TypeRep ty
ds_ev_typeable ty (EvTypeableTyCon evs)
  | Just (tc, ks) <- splitTyConApp_maybe ty
  = do { ctr <- dsLookupGlobalId mkPolyTyConAppName
                    -- mkPolyTyConApp :: TyCon -> [KindRep] -> [TypeRep] -> TypeRep
       ; tyRepTc <- dsLookupTyCon typeRepTyConName  -- TypeRep (the TyCon)
       ; let tyRepType = mkTyConApp tyRepTc []      -- TypeRep (the Type)
             mkRep cRep kReps tReps
               = mkApps (Var ctr) [ cRep
                                  , mkListExpr tyRepType kReps
                                  , mkListExpr tyRepType tReps ]


       ; tcRep <- tyConRep tc
       ; kReps <- zipWithM getRep evs ks
       ; return (mkRep tcRep kReps []) }

ds_ev_typeable ty (EvTypeableTyApp ev1 ev2)
  | Just (t1,t2) <- splitAppTy_maybe ty
  = do { e1  <- getRep ev1 t1
       ; e2  <- getRep ev2 t2
       ; ctr <- dsLookupGlobalId mkAppTyName
       ; return ( mkApps (Var ctr) [ e1, e2 ] ) }

ds_ev_typeable ty (EvTypeableTyLit ev)
  = do { fun  <- dsLookupGlobalId tr_fun
       ; dict <- dsEvTerm ev       -- Of type KnownNat/KnownSym
       ; let proxy = mkTyApps (Var proxyHashId) [ty_kind, ty]
       ; return (mkApps (mkTyApps (Var fun) [ty]) [ dict, proxy ]) }
  where
    ty_kind = typeKind ty

    -- tr_fun is the Name of
    --       typeNatTypeRep    :: KnownNat    a => Proxy# a -> TypeRep
    -- of    typeSymbolTypeRep :: KnownSymbol a => Proxy# a -> TypeRep
    tr_fun | ty_kind `eqType` typeNatKind    = typeNatTypeRepName
           | ty_kind `eqType` typeSymbolKind = typeSymbolTypeRepName
           | otherwise = panic "dsEvTypeable: unknown type lit kind"


ds_ev_typeable ty ev
  = pprPanic "dsEvTypeable" (ppr ty $$ ppr ev)

getRep :: EvTerm -> Type  -- EvTerm for Typeable ty, and ty
       -> DsM CoreExpr    -- Return CoreExpr :: TypeRep (of ty)
                          -- namely (typeRep# dict proxy)
-- Remember that
--   typeRep# :: forall k (a::k). Typeable k a -> Proxy k a -> TypeRep
getRep ev ty
  = do { typeable_expr <- dsEvTerm ev
       ; typeRepId     <- dsLookupGlobalId typeRepIdName
       ; let ty_args = [typeKind ty, ty]
       ; return (mkApps (mkTyApps (Var typeRepId) ty_args)
                        [ typeable_expr
                        , mkTyApps (Var proxyHashId) ty_args ]) }

tyConRep :: TyCon -> DsM CoreExpr
-- Returns CoreExpr :: TyCon
tyConRep tc
  | Just tc_rep_nm <- tyConRepName_maybe tc
  = do { tc_rep_id <- dsLookupGlobalId tc_rep_nm
       ; return (Var tc_rep_id) }
  | otherwise
  = pprPanic "tyConRep" (ppr tc)

{- Note [Memoising typeOf]
~~~~~~~~~~~~~~~~~~~~~~~~~~
See #3245, #9203

IMPORTANT: we don't want to recalculate the TypeRep once per call with
the proxy argument.  This is what went wrong in #3245 and #9203. So we
help GHC by manually keeping the 'rep' *outside* the lambda.
-}


{-**********************************************************************
*                                                                      *
           Desugaring EvCallStack evidence
*                                                                      *
**********************************************************************-}

dsEvCallStack :: EvCallStack -> DsM CoreExpr
-- See Note [Overview of implicit CallStacks] in TcEvidence.hs
dsEvCallStack cs = do
  df            <- getDynFlags
  m             <- getModule
  srcLocDataCon <- dsLookupDataCon srcLocDataConName
  let mkSrcLoc l =
        liftM (mkCoreConApps srcLocDataCon)
              (sequence [ mkStringExprFS (unitIdFS $ moduleUnitId m)
                        , mkStringExprFS (moduleNameFS $ moduleName m)
                        , mkStringExprFS (srcSpanFile l)
                        , return $ mkIntExprInt df (srcSpanStartLine l)
                        , return $ mkIntExprInt df (srcSpanStartCol l)
                        , return $ mkIntExprInt df (srcSpanEndLine l)
                        , return $ mkIntExprInt df (srcSpanEndCol l)
                        ])

  emptyCS <- Var <$> dsLookupGlobalId emptyCallStackName

  pushCSVar <- dsLookupGlobalId pushCallStackName
  let pushCS name loc rest =
        mkCoreApps (Var pushCSVar) [mkCoreTup [name, loc], rest]

  let mkPush name loc tm = do
        nameExpr <- mkStringExprFS name
        locExpr <- mkSrcLoc loc
        case tm of
          EvCallStack EvCsEmpty -> return (pushCS nameExpr locExpr emptyCS)
          _ -> do tmExpr  <- dsEvTerm tm
                  -- at this point tmExpr :: IP sym CallStack
                  -- but we need the actual CallStack to pass to pushCS,
                  -- so we use unwrapIP to strip the dictionary wrapper
                  -- See Note [Overview of implicit CallStacks]
                  let ip_co = unwrapIP (exprType tmExpr)
                  return (pushCS nameExpr locExpr (mkCastDs tmExpr ip_co))
  case cs of
    EvCsPushCall name loc tm -> mkPush (occNameFS $ getOccName name) loc tm
    EvCsEmpty -> return emptyCS
