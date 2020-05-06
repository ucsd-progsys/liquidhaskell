module Language.Haskell.Liquid.Bare.Typeclass
  ( makeClassDataDecl
  , elaborateClassDcp
  -- , stripDataConPPred
  )
where

import           Control.Monad                  ( forM )
import qualified Data.List                     as L
import qualified Data.HashSet                  as S
import qualified Data.Maybe                    as Mb
import qualified Language.Fixpoint.Types       as F
import qualified Language.Fixpoint.Misc        as Misc
import           Language.Haskell.Liquid.Bare.Elaborate
import qualified Language.Haskell.Liquid.GHC.Misc
                                               as GM
import qualified Language.Haskell.Liquid.GHC.API
                                               as Ghc
import qualified Language.Haskell.Liquid.Misc  as Misc
import qualified Language.Haskell.Liquid.Types.RefType
                                               as RT
import           Language.Haskell.Liquid.Types.Types

-- a list of class with user defined refinements
makeClassDataDecl :: [(Ghc.Class, [(Ghc.Id, LocBareType)])] -> [DataDecl]
makeClassDataDecl = fmap (uncurry classDeclToDataDecl)

-- TODO: I should have the knowledge to construct DataConP manually than
-- following the rather unwieldy pipeline: Resolved -> Unresolved -> Resolved.
-- maybe this should be fixed right after the GHC API refactoring?
classDeclToDataDecl :: Ghc.Class -> [(Ghc.Id, LocBareType)] -> DataDecl
classDeclToDataDecl cls refinedIds = DataDecl
  { tycName   = DnName (F.symbol <$> GM.locNamedThing cls)
  , tycTyVars = tyVars
  , tycPVars  = []
  , tycDCons  = [dctor]
  , tycSrcPos = F.loc . GM.locNamedThing $ cls
  , tycSFun   = Nothing
  , tycPropTy = Nothing
  , tycKind   = DataUser
  }
 where
  dctor = DataCtor { dcName   = F.dummyLoc $ F.symbol classDc
    -- YL: same as class tyvars??
    -- Ans: it's been working so far so probably yes
                   , dcTyVars = tyVars
    -- YL: what is theta?
    -- Ans: where class constraints should go yet remain unused
    -- maybe should factor this out?
                   , dcTheta  = []
                   , dcFields = fields
                   , dcResult = Nothing
                   }

  tyVars = F.symbol <$> Ghc.classTyVars cls

  fields = fmap attachRef classIds
  attachRef sid
    | Just ref <- L.lookup sid refinedIds
    = (F.symbol sid, RT.subts tyVarSubst (F.val ref))
    | otherwise
    = (F.symbol sid, RT.bareOfType . dropTheta . Ghc.varType $ sid)

  tyVarSubst = [ (GM.dropModuleUnique v, v) | v <- tyVars ]

  -- FIXME: dropTheta should not be needed as long as we 
  -- handle classes and ordinary data types separately
  -- Might be helpful if we add an additional field for
  -- typeclasses
  dropTheta :: Ghc.Type -> Ghc.Type
  dropTheta = Misc.thd3 . Ghc.tcSplitMethodTy

  classIds  = Ghc.classAllSelIds cls
  classDc   = Ghc.classDataCon cls



elaborateClassDcp
  :: (Ghc.CoreExpr -> F.Expr)
  -> (Ghc.CoreExpr -> Ghc.Ghc Ghc.CoreExpr)
  -> DataConP
  -> Ghc.Ghc (DataConP, DataConP)
elaborateClassDcp coreToLg simplifier dcp = do
  t' <- flip (zipWith addCoherenceOblig) prefts
    <$> forM fts (elaborateSpecType coreToLg simplifier)
  let ts' = elaborateMethod (F.symbol dc) (S.fromList xs) <$> t'
  pure
    ( dcp { dcpTyArgs = zip xs (stripPred <$> ts') }
    , dcp { dcpTyArgs = fmap (\(x, t) -> (x, strengthenTy x t)) (zip xs t') }
    )
 where
  addCoherenceOblig :: SpecType -> Maybe RReft -> SpecType
  addCoherenceOblig t Nothing  = t
  addCoherenceOblig t (Just r) = fromRTypeRep rrep
    { ty_res = res `RT.strengthen` r
    }
   where
    rrep = toRTypeRep t
    res  = ty_res rrep
  prefts =
    L.reverse
      .  take (length fts)
      $  fmap (Just . flip MkUReft mempty . mconcat) preftss
      ++ repeat Nothing
  preftss = (fmap . fmap) (uncurry (GM.coherenceObligToRef recsel))
                          (GM.buildCoherenceOblig cls)

  -- ugly, should have passed cls as an argument
  cls      = Mb.fromJust $ Ghc.tyConClass_maybe (Ghc.dataConTyCon dc)
  recsel   = F.symbol ("lq$recsel" :: String)
  resTy    = dcpTyRes dcp
  dc       = dcpCon dcp
  tvars    = (\x -> (makeRTVar x, mempty)) <$> dcpFreeTyVars dcp
      -- check if the names are qualified
  (xs, ts) = unzip (dcpTyArgs dcp)
  fts      = fullTy <$> ts
      -- turns forall a b. (a -> b) -> f a -> f b into
      -- forall f. Functor f => forall a b. (a -> b) -> f a -> f b
  stripPred :: SpecType -> SpecType
  stripPred = Misc.fourth4 . bkUnivClass
  fullTy :: SpecType -> SpecType
  fullTy t = mkArrow
    tvars
    []
    []
    [ ( recsel{- F.symbol dc-}
      , resTy
      , mempty
      )
    ]
    t
  strengthenTy :: F.Symbol -> SpecType -> SpecType
  strengthenTy x t = mkUnivs tvs pvs (RFun z cls (t' `RT.strengthen` mt) r)
   where
    (tvs, pvs, RFun z cls t' r) = bkUniv t
    vv = rTypeValueVar t'
    mt = RT.uReft (vv, F.PAtom F.Eq (F.EVar vv) (F.EApp (F.EVar x) (F.EVar z)))


elaborateMethod :: F.Symbol -> S.HashSet F.Symbol -> SpecType -> SpecType
elaborateMethod dc methods t = mapExprReft
  (\_ -> substClassOpBinding tcbind dc methods)
  t
 where
  tcbind = grabtcbind t
  grabtcbind :: SpecType -> F.Symbol
  grabtcbind t =
    F.notracepp "grabtcbind"
      $ case Misc.fst3 . Misc.snd3 . bkArrow . Misc.thd3 . bkUniv $ t of
          tcbind : _ -> tcbind
          []         -> impossible
            Nothing
            (  "elaborateMethod: inserted dictionary binder disappeared:"
            ++ F.showpp t
            )


-- Before: Functor.fmap ($p1Applicative $dFunctor)
-- After: Funcctor.fmap ($p1Applicative##GHC.Base.Applicative)
substClassOpBinding
  :: F.Symbol -> F.Symbol -> S.HashSet F.Symbol -> F.Expr -> F.Expr
substClassOpBinding tcbind dc methods e = go e
 where
  go :: F.Expr -> F.Expr
  go (F.EApp e0 e1)
    | F.EVar x <- e0, F.EVar y <- e1, y == tcbind, S.member x methods = F.EVar
      (x `F.suffixSymbol` dc)
    | otherwise = F.EApp (go e0) (go e1)
  go (F.ENeg e          ) = F.ENeg (go e)
  go (F.EBin bop e0 e1  ) = F.EBin bop (go e0) (go e1)
  go (F.EIte e0  e1 e2  ) = F.EIte (go e0) (go e1) (go e2)
  go (F.ECst e0     s   ) = F.ECst (go e0) s
  go (F.ELam (x, t) body) = F.ELam (x, t) (go body)
  go (F.PAnd es         ) = F.PAnd (go <$> es)
  go (F.POr  es         ) = F.POr (go <$> es)
  go (F.PNot e          ) = F.PNot (go e)
  go (F.PImp e0 e1      ) = F.PImp (go e0) (go e1)
  go (F.PIff e0 e1      ) = F.PIff (go e0) (go e1)
  go (F.PAtom brel e0 e1) = F.PAtom brel (go e0) (go e1)
  -- a catch-all binding is not a good idea
  go e                    = e
