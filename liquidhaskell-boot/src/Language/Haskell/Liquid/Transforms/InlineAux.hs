{-# LANGUAGE FlexibleContexts #-}

module Language.Haskell.Liquid.Transforms.InlineAux
  ( inlineAux
  )
where
import qualified Language.Haskell.Liquid.UX.Config  as UX
import           Liquid.GHC.API
import           Control.Arrow                  (second)
import qualified Language.Haskell.Liquid.GHC.Misc
                                               as GM
import qualified Data.HashMap.Strict           as M

-- | Inline auxiliary class method implementations in a 'CoreProgram'.
--
-- When GHC compiles a typeclass instance, it generates:
--   * a dictionary function (dfun), e.g. @$fShowInt@
--   * auxiliary functions for each method, e.g. @$cshow@ for 'show'
--
-- A call like @show $fShowInt x@ dispatches through the dictionary.
-- This pass rewrites such calls to bypass the dictionary and call the
-- auxiliary directly: @$cshow x@.
--
-- This transformation is only applied when 'UX.auxInline' is enabled in the
-- config. After inlining, 'occurAnalysePgm' is run to clean up dead bindings.
inlineAux :: UX.Config -> Module -> CoreProgram -> CoreProgram
inlineAux cfg m cbs =  if UX.auxInline cfg then occurAnalysePgm m (const False) (const False) [] (map f cbs) else cbs
 where
  -- For each binding that is itself an auxiliary (i.e. it appears as a free
  -- variable inside some dfun body), rewrite its RHS using 'inlineAuxExpr'.
  f :: CoreBind -> CoreBind
  f all'@(NonRec x e)
    | Just (dfunId, methodToAux) <- M.lookup x auxToMethodToAux = NonRec
      x
      (inlineAuxExpr dfunId methodToAux e)
    | otherwise = all'
  f (Rec bs) = Rec (fmap g bs)
   where
    g all'@(x, e)
      | Just (dfunId, methodToAux) <- M.lookup x auxToMethodToAux
      = (x, inlineAuxExpr dfunId methodToAux e)
      | otherwise
      = all'
  -- Build the combined map from every dfun found in the program.
  -- Maps each auxiliary Id to (its dfun, the method->aux map for that dfun).
  auxToMethodToAux = mconcat $ fmap (uncurry dfunIdSubst) (grepDFunIds cbs)

-- | Collect all dictionary-function bindings from a 'CoreProgram'.
--
-- A dfun is the implementation record GHC generates for a typeclass instance.
-- For example, @instance Show Int@ produces @$fShowInt :: Show Int@.
--
-- Example: given bindings for @[$fShowInt, foo, $fOrdInt]@, this returns
-- @[($fShowInt, <its RHS>), ($fOrdInt, <its RHS>)]@.
grepDFunIds :: CoreProgram -> [(DFunId, CoreExpr)]
grepDFunIds = filter (isDFunId . fst) . flattenBinds

-- | Check whether an 'OccName' is a GHC-generated class-op auxiliary name.
--
-- GHC names auxiliary class method implementations with the prefix @$c@.
-- For example, the auxiliary for 'show' in @instance Show Int@ is @$cshow@.
--
-- Examples:
--   isClassOpAuxOccName "$cshow"  == True
--   isClassOpAuxOccName "show"    == False
--   isClassOpAuxOccName "$fShowInt" == False
isClassOpAuxOccName :: OccName -> Bool
isClassOpAuxOccName occ = case occNameString occ of
  '$' : 'c' : _ -> True
  _             -> False

-- | Check whether @aux@ is the class-op auxiliary implementation of @method@.
--
-- @aux `isClassOpAuxOf` method@ holds when @aux@ has a @$c@-prefixed name
-- whose suffix matches @method@'s unqualified name.
--
-- Example:
--   -- aux   = "$cshow"  (OccName for the Show Int auxiliary)
--   -- method = "show"   (OccName for the 'show' selector)
--   "$cshow" `isClassOpAuxOf` "show" == True
--   "$cshow" `isClassOpAuxOf` "eq"   == False
isClassOpAuxOf :: Id -> Id -> Bool
isClassOpAuxOf aux method = case occNameString $ getOccName aux of
  '$' : 'c' : rest -> rest == occNameString (getOccName method)
  _                -> False

-- | Build a substitution map from a single dfun and its Core body.
--
-- For each auxiliary Id @aux@ that appears free in the dfun's body, and for
-- each class method @m@ such that @aux `isClassOpAuxOf` m@, the resulting map
-- contains an entry:
--
-- @   aux  ->  (dfunId, { m -> aux, ... })  @
--
-- This lets 'inlineAuxExpr' know that, inside the body of @aux@, calls to
-- method @m@ dispatched through @dfunId@ can be replaced by direct calls to
-- the corresponding auxiliary.
--
-- Example: for @$fShowInt@ whose body mentions @$cshow@ and @$cshowList@:
--
-- @
--   dfunIdSubst $fShowInt <body> ==
--     { $cshow     -> ($fShowInt, { show -> $cshow, showList -> $cshowList })
--     , $cshowList -> ($fShowInt, { show -> $cshow, showList -> $cshowList })
--     }
-- @
dfunIdSubst :: DFunId -> CoreExpr -> M.HashMap Id (Id, M.HashMap Id Id)
dfunIdSubst dfunId e = M.fromList [(auxId, (dfunId, methodToAux)) | auxId <- auxIds]
 where
  methodToAux = M.fromList
    [ (m, aux) | m <- methods, aux <- auxIds, aux `isClassOpAuxOf` m ]
  (_, _, cls, _) = tcSplitDFunTy (idType dfunId)
  auxIds = filter (isClassOpAuxOccName . getOccName) (exprFreeVarsList e)
  methods = classAllSelIds cls

-- | Rewrite a Core expression by replacing indirect method calls that go
-- through a dictionary with direct calls to the corresponding auxiliary.
--
-- The key rewrite rule (the last @go@ case before the @App@ fall-through) is:
--
-- @
--   m @T1 .. @Tn ($fC args..) x1 .. xk
--   -- where M.lookup m methodToAux == Just aux
--   ==>
--   aux args.. (go x1) .. (go xk)
-- @
--
-- In other words: a call to method @m@ whose first value argument is an
-- application of @dfunId@ is rewritten to call the auxiliary @aux@ directly,
-- passing the dfun's own arguments followed by the remaining method arguments.
--
-- All other sub-expressions are traversed recursively.
-- Dict-only let-bindings (@let x = dict in ...@) are substituted away eagerly
-- so that the main rewrite rule can fire on the resulting expression.
--
-- Example (schematic Core):
-- @
--   -- Before:
--   $cshow = \dict_arg ->
--     let d = $fShowInt in show @Int d 42
--
--   -- After inlineAuxExpr $fShowInt { show -> $cshow } on the RHS:
--   $cshow = \dict_arg ->
--     $cshow 42
-- @
inlineAuxExpr :: DFunId -> M.HashMap Id Id -> CoreExpr -> CoreExpr
inlineAuxExpr dfunId methodToAux = go
 where
  go :: CoreExpr -> CoreExpr
  go (Lam b body) = Lam b (go body)
  go (Let b body)
    | NonRec x e <- b, isDictId x =
        go $ substExpr (extendIdSubst emptySubst x e) body
    | otherwise = Let (mapBnd go b) (go body)
  go (Case e x t alts) = Case (go e) x t (fmap (mapAlt go) alts)
  go (Cast e c       ) = Cast (go e) c
  go (Tick t e       ) = Tick t (go e)
  go e
    | (Var m, args) <- collectArgs e
    , Just aux <- M.lookup m methodToAux
    , arg : argsNoTy <- dropWhile isTypeArg args
    , (Var x, argargs) <- collectArgs arg
    , x == dfunId
    = GM.notracePpr ("inlining in" ++ GM.showPpr e)
      $ mkCoreApps (Var aux) (argargs ++ (go <$> argsNoTy))
  go (App e0 e1) = App (go e0) (go e1)
  go e           = e


-- | Apply a transformation to the RHS expression(s) of a 'Bind'.
--
-- Example:
--   mapBnd go (NonRec x e)   == NonRec x (go e)
--   mapBnd go (Rec [(x,e)])  == Rec [(x, go e)]
mapBnd :: (Expr b -> Expr b) -> Bind b -> Bind b
mapBnd f (NonRec b e) = NonRec b (f e)
mapBnd f (Rec bs    ) = Rec (map (second f) bs)

-- | Apply a transformation to the body expression of a 'Case' alternative.
--
-- Example:
--   mapAlt go (Alt DataAlt [b] e) == Alt DataAlt [b] (go e)
mapAlt :: (Expr b -> Expr b) -> Alt b -> Alt b
mapAlt f (Alt d bs e) = Alt d bs (f e)
