{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

-- | Functions to make environments smaller
module Language.Fixpoint.Solver.EnvironmentReduction
  ( reduceEnvironments
  , simplifyBindings
  , dropLikelyIrrelevantBindings
  , inlineInSortedReft
  , mergeDuplicatedBindings
  , simplifyBooleanRefts
  , undoANF
  ) where

import           Control.Monad (guard, mplus, msum)
import           Data.Char (isUpper)
import           Data.Hashable (Hashable)
import           Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashMap.Strict as HashMap.Strict
import           Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import           Data.List (foldl', nub, partition)
import           Data.Maybe (fromMaybe)
import           Data.ShareMap (ShareMap)
import qualified Data.ShareMap as ShareMap
import qualified Data.Text as Text
import           Language.Fixpoint.SortCheck (exprSort_maybe)
import           Language.Fixpoint.Types.Config
import           Language.Fixpoint.Types.Constraints
import           Language.Fixpoint.Types.Environments
  ( BindEnv
  , BindId
  , IBindEnv
  , beBinds
  , diffIBindEnv
  , elemsIBindEnv
  , emptyIBindEnv
  , filterIBindEnv
  , fromListIBindEnv
  , insertsIBindEnv
  , insertBindEnv
  , lookupBindEnv
  , memberIBindEnv
  , unionIBindEnv
  , unionsIBindEnv
  )
import           Language.Fixpoint.Types.Names
  ( Symbol
  , anfPrefix
  , isPrefixOfSym
  , prefixOfSym
  , symbolText
  )
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Refinements
  ( Brel(..)
  , Expr(..)
  , KVar(..)
  , SortedReft(..)
  , Subst(..)
  , pattern PTrue
  , pattern PFalse
  , expr
  , exprKVars
  , exprSymbolsSet
  , mapPredReft
  , pAnd
  , reft
  , reftBind
  , reftPred
  , sortedReftSymbols
  , subst1
  )
import           Language.Fixpoint.Types.Sorts (boolSort, sortSymbols)
import           Language.Fixpoint.Types.Visitor (mapExprOnExpr)

-- | Strips from all the constraint environments the bindings that are
-- irrelevant for their respective constraints.
--
-- Environment reduction has the following stages.
--
-- Stage 1)
-- Compute the binding dependencies of each constraint ignoring KVars.
--
-- A binding is a dependency of a constraint if it is mentioned in the lhs, or
-- the rhs of the constraint, or in a binding that is a dependency, or in a
-- @define@ or @match@ clause that is mentioned in the lhs or rhs or another
-- binding dependency, or if it appears in the environment of the constraint and
-- can't be discarded as trivial (see 'dropIrrelevantBindings').
--
-- Stage 2)
-- Compute the binding dependencies of KVars.
--
-- A binding is a dependency of a KVar K1 if it is a dependency of a constraint
-- in which the K1 appears, or if it is a dependency of another KVar appearing
-- in a constraint in which K1 appears.
--
-- Stage 3)
-- Drop from the environment of each constraint the bindings that aren't
-- dependencies of the constraint, or that aren't dependencies of any KVar
-- appearing in the constraint.
--
--
-- Note on SInfo:
--
-- This function can be changed to work on 'SInfo' rather than 'FInfo'. However,
-- this causes some tests to fail. At least:
--
--    liquid-fixpoint/tests/proof/rewrite.fq
--    tests/import/client/ReflectClient4a.hs
--
-- lhs bindings are numbered with the highest numbers when FInfo
-- is converted to SInfo. Environment reduction, however, rehashes
-- the binding identifiers and lhss could end up with a lower numbering.
-- For most of the tests, this doesn't seem to make a difference, but it
-- causes the two tests referred above to fail.
--
-- See #473 for more discussion.
--
reduceEnvironments :: FInfo a -> FInfo a
reduceEnvironments fi =
  let constraints = HashMap.Strict.toList $ cm fi
      aenvMap = axiomEnvSymbols (ae fi)
      reducedEnvs = map (reduceConstraintEnvironment (bs fi) aenvMap) constraints
      (cm', ws') = reduceWFConstraintEnvironments (bs fi) (reducedEnvs, ws fi)
      bs' = (bs fi) { beBinds = dropBindsMissingFrom (beBinds $ bs fi) cm' ws' }

   in fi
     { bs = bs'
     , cm = HashMap.fromList cm'
     , ws = ws'
     , ebinds = updateEbinds bs' (ebinds fi)
     , bindInfo = updateBindInfoKeys bs' $ bindInfo fi
     }

  where
    dropBindsMissingFrom
      :: HashMap BindId (Symbol, SortedReft)
      -> [(SubcId, SubC a)]
      -> HashMap KVar (WfC a)
      -> HashMap BindId (Symbol, SortedReft)
    dropBindsMissingFrom be cs ws =
      let ibindEnv = unionsIBindEnv $
            map (senv . snd) cs ++
            map wenv (HashMap.elems ws)
       in
          HashMap.filterWithKey (\bId _ -> memberIBindEnv bId ibindEnv) be

    -- Updates BindIds in an ebinds list
    updateEbinds be = filter (`HashMap.member` beBinds be)

    -- Updates BindId keys in a bindInfos map
    updateBindInfoKeys be oldBindInfos =
      HashMap.intersection oldBindInfos (beBinds be)

-- | Reduces the environments of WF constraints.
--
-- @reduceWFConstraintEnvironments bindEnv (cs, ws)@
--  * enlarges the environments in cs with bindings needed by the kvars they use
--  * replaces the environment in ws with reduced environments
--
-- Reduction of wf environments gets rid of any bindings not mentioned by
-- 'relatedKVarBinds' or any substitution on the corresponding KVar anywhere.
--
reduceWFConstraintEnvironments
  :: BindEnv    -- ^ Environment before reduction
  -> ([ReducedConstraint a], HashMap KVar (WfC a))
     -- ^ @(cs, ws)@:
     --  * @cs@ are the constraints with reduced environments
     --  * @ws@ are the wf constraints in which to reduce environments
  -> ([(SubcId, SubC a)], HashMap KVar (WfC a))
reduceWFConstraintEnvironments bindEnv (cs, wfs) =
  let
      (kvarsBinds, kvarSubstSymbols, kvarsBySubC) = relatedKVarBinds bindEnv cs

      wfBindsPlusSortSymbols =
        HashMap.unionWith HashSet.union kvarsBinds $
        HashMap.map (sortSymbols . (\(_, b, _) -> b) . wrft) wfs

      kvarsRelevantBinds =
        HashMap.unionWith HashSet.union wfBindsPlusSortSymbols $
        kvarSubstSymbols

      ws' =
        HashMap.mapWithKey
          (reduceWFConstraintEnvironment bindEnv kvarsRelevantBinds)
          wfs

      wsSymbols = HashMap.map (asSymbolSet bindEnv . wenv) ws'

      kvarsWsBinds =
        HashMap.unionWith HashSet.intersection wfBindsPlusSortSymbols wsSymbols

      cs' = zipWith
              (updateSubcEnvsWithKVarBinds bindEnv kvarsWsBinds)
              kvarsBySubC
              cs
   in
      (cs', ws')

  where
    -- Initially, the constraint environment only includes the information
    -- relevant to the rhs and the lhs. If a kvar is present, it may need
    -- additional bindings that are required by the kvar. These are added
    -- in this function.
    updateSubcEnvsWithKVarBinds
      :: BindEnv
      -> HashMap KVar (HashSet Symbol)
      -> [KVar]
      -> ReducedConstraint a
      -> (SubcId, SubC a)
    updateSubcEnvsWithKVarBinds be kvarsBinds kvs c =
      let updateIBindEnv oldEnv =
            unionIBindEnv (reducedEnv c) $
            if null kvs then emptyIBindEnv
            else fromListIBindEnv
              [ bId
              | bId <- elemsIBindEnv oldEnv
              , let (s, _sr) = lookupBindEnv bId be
              , any (neededByKVar s) kvs
              ]
          neededByKVar s kv =
            case HashMap.lookup kv kvarsBinds of
              Nothing -> False
              Just kbindSyms -> HashSet.member s kbindSyms
       in (constraintId c, updateSEnv (originalConstraint c) updateIBindEnv)

    -- @reduceWFConstraintEnvironment be kbinds k c@ drops bindings from @c@
    -- that aren't present in @kbinds ! k@.
    reduceWFConstraintEnvironment
      :: BindEnv
      -> HashMap KVar (HashSet Symbol)
      -> KVar
      -> WfC a
      -> WfC a
    reduceWFConstraintEnvironment bindEnv kvarBinds k c =
      case HashMap.lookup k kvarBinds of
        Nothing -> c { wenv = emptyIBindEnv }
        Just kbindSymbols ->
          c { wenv = filterIBindEnv (relevantBindIds kbindSymbols) (wenv c) }
      where
        relevantBindIds :: HashSet Symbol -> BindId -> Bool
        relevantBindIds kbindSymbols bId =
          let (s, _) = lookupBindEnv bId bindEnv
           in HashSet.member s kbindSymbols

data ReducedConstraint a = ReducedConstraint
  { reducedEnv :: IBindEnv       -- ^ Environment which has been reduced
  , originalConstraint :: SubC a -- ^ The original constraint
  , constraintId :: SubcId       -- ^ Id of the constraint
  }

reduceConstraintEnvironment
  :: BindEnv
  -> HashMap Symbol (HashSet Symbol)
  -> (SubcId, SubC a)
  -> ReducedConstraint a
reduceConstraintEnvironment bindEnv aenvMap (cid, c) =
  let env = [ (s, bId, sr)
            | bId <- elemsIBindEnv $ senv c
            , let (s, sr) = lookupBindEnv bId bindEnv
            ]
      prunedEnv =
        fromListIBindEnv
        [ bId | (_, bId, _) <- dropIrrelevantBindings aenvMap constraintSymbols env ]
      constraintSymbols =
        HashSet.union (sortedReftSymbols $ slhs c) (sortedReftSymbols $ srhs c)
   in ReducedConstraint
        { reducedEnv = prunedEnv
        , originalConstraint = c
        , constraintId = cid
        }

-- | @dropIrrelevantBindings aenvMap ss env@ drops bindings from @env@ which
-- aren't referenced neither in a refinement type in the environment nor in
-- @ss@, and not reachable in definitions of @aenv@ referred from @env@ or
-- @ss@, and which can't possibly affect the outcome of verification.
--
-- Right now, it drops bindings of the form @a : {v | true }@ and
-- @b : {v | v [>=|<=|=|!=|etc] e }@
-- whenever @a@ and @b@ aren't referenced from any formulas.
--
dropIrrelevantBindings
  :: HashMap Symbol (HashSet Symbol)
  -> HashSet Symbol
  -> [(Symbol, BindId, SortedReft)]
  -> [(Symbol, BindId, SortedReft)]
dropIrrelevantBindings aenvMap extraSymbols env =
  filter relevantBind env
  where
    allSymbols =
      reachableSymbols (HashSet.union extraSymbols envSymbols) aenvMap
    envSymbols =
      HashSet.unions $ map (\(_, _, sr) -> sortedReftSymbols sr) env

    relevantBind (s, _, sr)
      | HashSet.member s allSymbols = True
      | otherwise = case reftPred (sr_reft sr) of
          PTrue -> False
          PAtom _ (dropECst -> EVar sym) _e -> sym /= reftBind (sr_reft sr)
          PAtom _ _e (dropECst -> EVar sym) -> sym /= reftBind (sr_reft sr)
          _ -> True

-- | For each Equation and Rewrite, collects the symbols that it needs.
axiomEnvSymbols :: AxiomEnv -> HashMap Symbol (HashSet Symbol)
axiomEnvSymbols ae =
  HashMap.union
    (HashMap.fromList $ map eqSymbols $ aenvEqs ae)
    (HashMap.fromList $ map rewriteSymbols $ aenvSimpl ae)
  where
    eqSymbols eq =
      let bodySymbols =
            HashSet.difference
              (exprSymbolsSet (eqBody eq) `HashSet.union` sortSymbols (eqSort eq))
              (HashSet.fromList $ map fst $ eqArgs eq)
          sortSyms = HashSet.unions $ map (sortSymbols . snd) $ eqArgs eq
          allSymbols =
            if eqRec eq then
              HashSet.insert (eqName eq) (bodySymbols `HashSet.union` sortSyms)
            else
              bodySymbols `HashSet.union` sortSyms
       in
          (eqName eq, allSymbols)

    rewriteSymbols rw =
      let bodySymbols =
            HashSet.difference
              (exprSymbolsSet (smBody rw))
              (HashSet.fromList $ smArgs rw)
          rwSymbols = HashSet.insert (smDC rw) bodySymbols
       in (smName rw, rwSymbols)

unconsHashSet :: (Hashable a, Eq a) => HashSet a -> Maybe (a, HashSet a)
unconsHashSet xs = case HashSet.toList xs of
  [] -> Nothing
  (x : _) -> Just (x, HashSet.delete x xs)

setOf :: (Hashable k, Eq k) => HashMap k (HashSet a) -> k -> HashSet a
setOf m x = fromMaybe HashSet.empty (HashMap.lookup x m)

mapOf :: (Hashable k, Eq k) => HashMap k (HashMap a b) -> k -> HashMap a b
mapOf m x = fromMaybe HashMap.empty (HashMap.lookup x m)

-- @relatedKVarBinds binds cs@ yields:
-- 1) the set of all bindings that might be needed by each KVar mentioned
-- in the constraints @cs@, and
-- 2) the set of symbols appearing in substitutions of the KVar in any
-- constraint. That is: @kv@ is associated with @i@, @j@, and @h@ if there
-- is some constraint with the KVar substitution @kv[i:=e0][j:=e1]@ and
-- some constraint with the KVar substitution @kv[h:=e2]@ appearing in
-- the rhs, lhs, or the environment.
-- 3) The list of kvars used in each constraint.
--
-- We assume that if a KVar is mentioned in a constraint or in its
-- environment, then all the bindings in the environment of the constraint
-- might be needed by the KVar.
--
-- Moreover, if two KVars are mentioned together in the same constraint,
-- then the bindings that might be needed for either of them might
-- be needed by the other.
--
relatedKVarBinds
  :: BindEnv
  -> [ReducedConstraint a]
  -> (HashMap KVar (HashSet Symbol), HashMap KVar (HashSet Symbol), [[KVar]])
relatedKVarBinds bindEnv cs =
  let kvarsSubstSymbolsBySubC = map kvarBindsFromSubC cs
      kvarsBySubC = map HashMap.keys kvarsSubstSymbolsBySubC
      bindIdsByKVar =
       ShareMap.toHashMap $
       ShareMap.map (asSymbolSet bindEnv) $
       groupIBindEnvByKVar $ zip (map reducedEnv cs) kvarsBySubC
      substsByKVar =
        foldl' (HashMap.unionWith HashSet.union) HashMap.empty kvarsSubstSymbolsBySubC
   in
      (bindIdsByKVar, substsByKVar, kvarsBySubC)
  where
    kvarsByBindId :: HashMap BindId (HashMap KVar [Subst])
    kvarsByBindId =
      HashMap.map (exprKVars . reftPred . sr_reft . snd) $ beBinds bindEnv

    -- Returns all of the KVars used in the constraint, together with
    -- the symbols that appear in substitutions of those KVars.
    kvarBindsFromSubC :: ReducedConstraint a -> HashMap KVar (HashSet Symbol)
    kvarBindsFromSubC sc =
      let c = originalConstraint sc
          unSubst (Su su) = su
          substsToHashSet =
            HashSet.fromMap . HashMap.map (const ()) . HashMap.unions . map unSubst
       in foldl' (HashMap.unionWith HashSet.union) HashMap.empty $
          map (HashMap.map substsToHashSet) $
          (exprKVars (reftPred $ sr_reft $ srhs c) :) $
          (exprKVars (reftPred $ sr_reft $ slhs c) :) $
          map (mapOf kvarsByBindId) $
          elemsIBindEnv (reducedEnv sc)

    -- @groupIBindEnvByKVar kvs@ is a map of KVars to all the bindings that
    -- they can potentially use.
    --
    -- @kvars@ tells for each environment what KVars it uses.
    groupIBindEnvByKVar :: [(IBindEnv, [KVar])] -> ShareMap KVar IBindEnv
    groupIBindEnvByKVar = foldl' mergeBinds ShareMap.empty

    -- @mergeBinds sm bs (bindIds, kvars)@ merges the binds used by all KVars in
    -- @kvars@ and also adds to the result the bind Ids in @bindIds@.
    mergeBinds
      :: ShareMap KVar IBindEnv
      -> (IBindEnv, [KVar])
      -> ShareMap KVar IBindEnv
    mergeBinds sm (bindIds, kvars) = case kvars of
      [] -> sm
      k : ks ->
        let sm' = ShareMap.insertWith unionIBindEnv k bindIds sm
         in foldr (ShareMap.mergeKeysWith unionIBindEnv k) sm' ks

asSymbolSet :: BindEnv -> IBindEnv -> HashSet Symbol
asSymbolSet be ibinds =
  HashSet.fromList
    [ s
    | bId <- elemsIBindEnv ibinds
    , let (s, _) = lookupBindEnv bId be
    ]

-- | @reachableSymbols x r@ computes the set of symbols reachable from @x@
-- in the graph represented by @r@. Includes @x@ in the result.
reachableSymbols :: HashSet Symbol -> HashMap Symbol (HashSet Symbol) -> HashSet Symbol
reachableSymbols ss0 outgoingEdges = go HashSet.empty ss0
  where
    -- @go acc ss@ contains @acc@ and @ss@ plus any symbols reachable from @ss@
    go :: HashSet Symbol -> HashSet Symbol -> HashSet Symbol
    go acc ss = case unconsHashSet ss of
      Nothing -> acc
      Just (x, xs) ->
        if x `HashSet.member` acc then go acc xs
        else
          let relatedToX = setOf outgoingEdges x
           in go (HashSet.insert x acc) (HashSet.union relatedToX xs)

-- | Simplifies bindings in constraint environments.
--
-- It runs 'mergeDuplicatedBindings' and 'simplifyBooleanRefts'
-- on the environment of each constraint.
--
-- If 'inlineANFBindings cfg' is on, also runs 'undoANF' to inline
-- @lq_anf@ bindings.
simplifyBindings :: Config -> FInfo a -> FInfo a
simplifyBindings cfg fi =
  let (bs', cm', oldToNew) = simplifyConstraints (bs fi) (cm fi)
   in fi
        { bs = bs'
        , cm = cm'
        , ebinds = updateEbinds oldToNew (ebinds fi)
        , bindInfo = updateBindInfoKeys oldToNew $ bindInfo fi
        }
  where
    updateEbinds :: HashMap BindId [BindId] -> [BindId] -> [BindId]
    updateEbinds oldToNew ebs =
      nub $
      concat [ bId : fromMaybe [] (HashMap.lookup bId oldToNew) | bId <- ebs ]

    updateBindInfoKeys
      :: HashMap BindId [BindId] -> HashMap BindId a -> HashMap BindId a
    updateBindInfoKeys oldToNew infoMap =
      HashMap.fromList
        [ (n, a)
        | (bId, a) <- HashMap.toList infoMap
        , Just news <- [HashMap.lookup bId oldToNew]
        , n <- bId : news
        ]

    simplifyConstraints
      :: BindEnv
      -> HashMap SubcId (SubC a)
      -> (BindEnv, HashMap SubcId (SubC a), HashMap BindId [BindId])
    simplifyConstraints be cs =
      let (be', cs', newToOld) =
             HashMap.foldlWithKey' simplifyConstraintBindings (be, [], []) cs
          oldToNew =
            HashMap.fromListWith (++) $
            concatMap (\(n, olds) -> map (\o -> (o, [n])) olds) newToOld
       in
          (be', HashMap.fromList cs', oldToNew)

    simplifyConstraintBindings
      :: (BindEnv, [(SubcId, SubC a)], [(BindId, [BindId])])
      -> SubcId
      -> SubC a
      -> (BindEnv, [(SubcId, SubC a)], [(BindId, [BindId])])
    simplifyConstraintBindings (bindEnv, cs, newToOld) cid c =
      let env =
            [ (s, ([bId], sr))
            | bId <- elemsIBindEnv $ senv c
            , let (s, sr) = lookupBindEnv bId bindEnv
            ]

          mergedEnv = mergeDuplicatedBindings env
          undoANFEnv =
            if inlineANFBindings cfg then undoANF mergedEnv else HashMap.empty
          boolSimplEnv =
            simplifyBooleanRefts $ HashMap.union undoANFEnv mergedEnv

          modifiedBinds = HashMap.toList $ HashMap.union boolSimplEnv undoANFEnv

          modifiedBindIds = map (fst . snd) modifiedBinds

          unchangedBindIds = senv c `diffIBindEnv` fromListIBindEnv (concat modifiedBindIds)

          (newBindIds, bindEnv') = insertBinds ([], bindEnv) modifiedBinds

          newIBindEnv = insertsIBindEnv newBindIds unchangedBindIds

          newToOld' = zip newBindIds modifiedBindIds ++ newToOld
       in
          (bindEnv', (cid, updateSEnv c (const newIBindEnv)) : cs, newToOld')

    insertBinds = foldl' $ \(xs, be) (s, (_, sr)) ->
      let (bId, be') = insertBindEnv s sr be
       in (bId : xs, be')

-- | If the environment contains duplicated bindings, they are
-- combined with conjunctions.
--
-- This means that @[ a : {v | P v }, a : {z | Q z }, b : {v | S v} ]@
-- is combined into @[ a : {v | P v && Q v }, b : {v | S v} ]@
--
-- If a symbol has two bindings with different sorts, none of the bindings
-- for that symbol are merged.
mergeDuplicatedBindings
  :: Semigroup m
  => [(Symbol, (m, SortedReft))]
  -> HashMap Symbol (m, SortedReft)
mergeDuplicatedBindings xs =
    HashMap.mapMaybe dropNothings $
    HashMap.fromListWith mergeSortedReft $
    map (fmap (fmap Just)) xs
  where
    dropNothings (m, msr) = (,) m <$> msr

    mergeSortedReft (bs0, msr0) (bs1, msr1) =
      let msr = do
            sr0 <- msr0
            sr1 <- msr1
            guard (sr_sort sr0 == sr_sort sr1)
            Just sr0 { sr_reft = mergeRefts (sr_reft sr0) (sr_reft sr1) }
       in
          (bs0 <> bs1, msr)

    mergeRefts r0 r1 =
      reft
        (reftBind r0)
        (pAnd
          [ reftPred r0
          , subst1 (reftPred r1) (reftBind r1, expr (reftBind r0))
          ]
        )

-- | Inlines some of the bindings introduced by ANF normalization
-- at their use sites.
--
-- Only modified bindings are returned.
--
-- Only bindings with prefix lq_anf... might be inlined.
--
-- This function is used to produced the prettified output, and the user
-- can request to use it in the verification pipeline with
-- @--inline-anf-bindings@. However, using it in the verification
-- pipeline causes some tests in liquidhaskell to blow up.
undoANF :: HashMap Symbol (m, SortedReft) -> HashMap Symbol (m, SortedReft)
undoANF env =
    -- Circular program here. This should terminate as long as the
    -- bindings introduced by ANF don't form cycles.
    let env' = HashMap.map (inlineInSortedReftChanged env') env
     in HashMap.mapMaybe dropUnchanged env'
  where
    dropUnchanged ((m, b), sr) = do
      guard b
      Just (m, sr)

inlineInSortedReft
  :: HashMap Symbol (m, SortedReft) -> SortedReft -> SortedReft
inlineInSortedReft env sr =
  snd $ inlineInSortedReftChanged env (error "never should evaluate", sr)

-- | Inlines bindings in env in the given 'SortedReft'.
-- Attaches a 'Bool' telling if the 'SortedReft' was changed.
inlineInSortedReftChanged
  :: HashMap Symbol (a, SortedReft)
  -> (m, SortedReft)
  -> ((m, Bool), SortedReft)
inlineInSortedReftChanged env (m, sr) =
  let e = reftPred (sr_reft sr)
      e' = inlineInExpr env e
   in ((m, e /= e'), sr { sr_reft = mapPredReft (const e') (sr_reft sr) })

-- | Inlines bindings preffixed with @lq_anf@ in the given expression
-- if they appear in equalities.
--
-- Given a binding like @a : { v | v = e1 && e2 }@ and an expression @... e0 = a ...@,
-- this function produces the expression @... e0 = e1 ...@
-- if @v@ does not appear free in @e1@.
--
-- @... e0 = (a : s) ...@ is equally transformed to
-- @... e0 = (e1 : s) ...@
--
-- Given a binding like @a : { v | v = e1 }@ and an expression @... a ...@,
-- this function produces the expression @... e1 ...@ if @v@ does not
-- appear free in @e1@.
--
-- The first parameter indicates the maximum amount of conjuncts that a
-- binding is allowed to have. If the binding exceeds this threshold, it
-- is not inlined.
inlineInExpr :: HashMap Symbol (m, SortedReft) -> Expr -> Expr
inlineInExpr env = simplify . mapExprOnExpr inlineExpr
  where
    inlineExpr (EVar sym)
      | anfPrefix `isPrefixOfSym` sym
      , Just (_, sr) <- HashMap.lookup sym env
      , let r = sr_reft sr
      , Just e <- isSingletonE (reftBind r) (reftPred r)
      = wrapWithCoercion Eq (sr_sort sr) e
    inlineExpr (PAtom br e0 e1@(dropECst -> EVar sym))
      | anfPrefix `isPrefixOfSym` sym
      , isEq br
      , Just (_, sr) <- HashMap.lookup sym env
      , let r = sr_reft sr
      , Just e <- isSingletonE (reftBind r) (reftPred r)
      =
        PAtom br e0 $ subst1 e1 (sym, wrapWithCoercion br (sr_sort sr) e)
    inlineExpr e = e

    isSingletonE v (PAtom br e0 e1)
      | isEq br = isSingEq v e0 e1 `mplus` isSingEq v e1 e0
    isSingletonE v (PIff e0 e1) =
      isSingEq v e0 e1 `mplus` isSingEq v e1 e0
    isSingletonE v (PAnd cs) =
      msum $ map (isSingletonE v) cs
    isSingletonE _ _ =
      Nothing

    isSingEq v e0 e1 = do
      guard $ EVar v == dropECst e0 && not (HashSet.member v $ exprSymbolsSet e1)
      Just e1

    isEq r = r == Eq || r == Ueq

    wrapWithCoercion br to e = case exprSort_maybe e of
      Just from -> if from /= to then ECoerc from to e else e
      Nothing -> if br == Ueq then ECst e to else e

dropECst :: Expr -> Expr
dropECst = \case
  ECst e _t -> dropECst e
  e -> e

-- | Transforms bindings of the form @{v:bool | v && P v}@ into
-- @{v:Bool | v && P true}@, and bindings of the form @{v:bool | ~v && P v}@
-- into @{v:bool | ~v && P false}@.
--
-- Only yields the modified bindings.
simplifyBooleanRefts
  :: HashMap Symbol (m, SortedReft) -> HashMap Symbol (m, SortedReft)
simplifyBooleanRefts = HashMap.mapMaybe simplifyBooleanSortedReft
  where
    simplifyBooleanSortedReft (m, sr)
      | sr_sort sr == boolSort
      , let r = sr_reft sr
      , Just (e, rest) <- symbolUsedAtTopLevelAnd (reftBind r) (reftPred r)
      = let e' = pAnd $ e : map (`subst1` (reftBind r, atomToBool e)) rest
            atomToBool a = if a == EVar (reftBind r) then PTrue else PFalse
         in Just (m, sr { sr_reft = mapPredReft (const e') r })
    simplifyBooleanSortedReft _ = Nothing

    symbolUsedAtTopLevelAnd s (PAnd ps) =
      findExpr (EVar s) ps `mplus` findExpr (PNot (EVar s)) ps
    symbolUsedAtTopLevelAnd _ _ = Nothing

    findExpr e es = do
      case partition (e ==) es of
        ([], _) -> Nothing
        (e:_, rest) -> Just (e, rest)

-- | @dropLikelyIrrelevantBindings ss env@ is like @dropIrrelevantBindings@
-- but drops bindings that could potentially be necessary to validate a
-- constraint.
--
-- This function drops any bindings in the reachable set of symbols of @ss@.
-- See 'relatedSymbols'.
--
-- A constraint might be rendered unverifiable if the verification depends on
-- the environment being inconsistent. For instance, suppose the constraint
-- is @a < 0@ and we call this function like
--
-- > dropLikelyIrrelevantBindings ["a"] [a : { v | v > 0 }, b : { v | false }]
-- >   == [a : { v | v > 0 }]
--
-- The binding for @b@ is dropped since it is not otherwise related to @a@,
-- making the corresponding constraint unverifiable.
--
-- Bindings refered only from @match@ or @define@ clauses will be dropped as
-- well.
--
-- Symbols starting with a capital letter will be dropped too, as these are
-- usually global identifiers with either uninteresting or known types.
--
dropLikelyIrrelevantBindings
  :: HashSet Symbol
  -> HashMap Symbol SortedReft
  -> HashMap Symbol SortedReft
dropLikelyIrrelevantBindings ss env = HashMap.filterWithKey relevant env
  where
    relatedSyms = relatedSymbols ss env
    relevant s _sr =
      (not (capitalizedSym s) || prefixOfSym s /= s) && s `HashSet.member` relatedSyms
    capitalizedSym = Text.all isUpper . Text.take 1 . symbolText

-- | @relatedSymbols ss env@ is the set of all symbols used transitively
-- by @ss@ in @env@ or used together with it in a refinement type.
-- The output includes @ss@.
--
-- For instance, say @ss@ contains @a@, and the environment is
--
-- > a : { v | v > b }, b : int, c : { v | v >= b && b >= d}, d : int
--
-- @a@ uses @b@. Because the predicate of @c@ relates @b@ with @d@,
-- @d@ can also influence the validity of the predicate of @a@, and therefore
-- we include both @b@, @c@, and @d@ in the set of related symbols.
relatedSymbols :: HashSet Symbol -> HashMap Symbol SortedReft -> HashSet Symbol
relatedSymbols ss0 env = go HashSet.empty ss0
  where
    directlyUses = HashMap.map (exprSymbolsSet . reftPred . sr_reft) env
    usedBy = HashMap.fromListWith HashSet.union
               [ (x, HashSet.singleton s)
               | (s, xs) <- HashMap.toList directlyUses
               , x <- HashSet.toList xs
               ]

    -- @go acc ss@ contains @acc@ and @ss@ plus any symbols reachable from @ss@
    go :: HashSet Symbol -> HashSet Symbol -> HashSet Symbol
    go acc ss = case unconsHashSet ss of
      Nothing -> acc
      Just (x, xs) ->
        if x `HashSet.member` acc then go acc xs
        else
          let usersOfX = usedBy `setOf` x
              relatedToX = HashSet.unions $
                usersOfX : map (directlyUses `setOf`) (x : HashSet.toList usersOfX)
           in go (HashSet.insert x acc) (HashSet.union relatedToX xs)
