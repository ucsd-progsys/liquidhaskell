{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ViewPatterns          #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE FlexibleContexts      #-}


module Language.Haskell.Liquid.Constraint.Qualifier
  ( qualifiers
  , useSpcQuals
  )
  where

import           Prelude hiding (error)
import           Data.List                (delete, nub)
import           Data.Maybe               (isJust, catMaybes, fromMaybe, isNothing)
import qualified Data.HashSet        as S
import qualified Data.HashMap.Strict as M
import           Debug.Trace (trace)
import           TyCon
import           Var (Var)
import           Language.Fixpoint.Types                  hiding (panic, mkQual)
import qualified Language.Fixpoint.Types.Config as FC
import           Language.Fixpoint.SortCheck
import           Language.Haskell.Liquid.Bare
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.GHC.Misc         (getSourcePos)
import           Language.Haskell.Liquid.Misc             (condNull)
import           Language.Haskell.Liquid.Types.PredType
import           Language.Haskell.Liquid.Types


--------------------------------------------------------------------------------
qualifiers :: GhcInfo -> SEnv Sort -> [Qualifier]
--------------------------------------------------------------------------------
qualifiers info lEnv
  =  condNull (useSpcQuals info) (gsQualifiers $ spec info)
  ++ condNull (useSigQuals info) (sigQualifiers  info lEnv)
  ++ condNull (useAlsQuals info) (alsQualifiers  info lEnv)

-- --------------------------------------------------------------------------------
-- qualifiers :: GhcInfo -> SEnv Sort -> [Qualifier]
-- --------------------------------------------------------------------------------
-- qualifiers info env = spcQs ++ genQs
  -- where
    -- spcQs           = gsQualifiers spc
    -- genQs           = specificationQualifiers info env
    -- n               = maxParams (getConfig spc)
    -- spc             = spec info

maxQualParams :: (HasConfig t) => t -> Int
maxQualParams = maxParams . getConfig

-- | Use explicitly given qualifiers .spec or source (.hs, .lhs) files
useSpcQuals :: (HasConfig t) => t -> Bool
useSpcQuals i = useQuals i && not (useAlsQuals i)

-- | Scrape qualifiers from function signatures (incr :: x:Int -> {v:Int | v > x})
useSigQuals :: (HasConfig t) => t -> Bool
useSigQuals i = useQuals i && not (useAlsQuals i)

-- | Scrape qualifiers from refinement type aliases (type Nat = {v:Int | 0 <= 0})
useAlsQuals :: (HasConfig t) => t -> Bool
useAlsQuals i = useQuals i && i `hasOpt` higherOrderFlag && not (needQuals i)

useQuals :: (HasConfig t) => t -> Bool
useQuals = not . (FC.All == ) . eliminate . getConfig

needQuals :: (HasConfig t) => t -> Bool
needQuals = (FC.None == ) . eliminate . getConfig

--------------------------------------------------------------------------------
alsQualifiers :: GhcInfo -> SEnv Sort -> [Qualifier]
--------------------------------------------------------------------------------
alsQualifiers info lEnv
  = [ q | a <- specAliases info
        , q <- refTypeQuals lEnv (rtPos a) tce (rtBody a)
        , length (qParams q) <= k + 1
        , validQual lEnv q
    ]
    where
      k   = maxQualParams info
      tce = gsTcEmbeds (spec info)

    -- Symbol (RTAlias RTyVar SpecType)

specAliases :: GhcInfo -> [RTAlias RTyVar SpecType]
specAliases = M.elems . typeAliases . gsRTAliases . spec

validQual :: SEnv Sort -> Qualifier -> Bool
validQual lEnv q = isJust $ checkSortExpr env (qBody q)
  where
    env          = unionSEnv lEnv qEnv
    qEnv         = M.fromList (qParams q)

--------------------------------------------------------------------------------
sigQualifiers :: GhcInfo -> SEnv Sort -> [Qualifier]
--------------------------------------------------------------------------------
sigQualifiers info lEnv
  = [ q | (x, t) <- specBinders info
        , x `S.member` qbs
        , q <- refTypeQuals lEnv (getSourcePos x) tce (val t)
        -- NOTE: large qualifiers are VERY expensive, so we only mine
        -- qualifiers up to a given size, controlled with --max-params
        , length (qParams q) <= k + 1
    ]
    where
      k   = maxQualParams info
      tce = gsTcEmbeds (spec info)
      qbs = qualifyingBinders info

qualifyingBinders :: GhcInfo -> S.HashSet Var
qualifyingBinders info = S.difference sTake sDrop
  where
    sTake              = S.fromList $ defVars info ++ useVars info ++ scrapeVars info
    sDrop              = S.fromList $ specAxiomVars info

-- NOTE: this mines extra, useful qualifiers but causes
-- a significant increase in running time, so we hide it
-- behind `--scrape-imports` and `--scrape-used-imports`
scrapeVars :: GhcInfo -> [Var]
scrapeVars info
  | info `hasOpt` scrapeUsedImports = useVars info
  | info `hasOpt` scrapeImports     = impVars info
  | otherwise                       = []

specBinders :: GhcInfo -> [(Var, LocSpecType)]
specBinders info = mconcat
  [ gsTySigs  sp
  , gsAsmSigs sp
  , gsCtors   sp
  , if info `hasOpt` scrapeInternals then gsInSigs sp else []
  ]
  where
    sp  = spec info

specAxiomVars :: GhcInfo -> [Var]
specAxiomVars =  gsReflects . spec

-- GRAVEYARD: scraping quals from imports kills the system with too much crap
-- specificationQualifiers info = {- filter okQual -} qs
--   where
--     qs                       = concatMap refTypeQualifiers ts
--     refTypeQualifiers        = refTypeQuals $ tcEmbeds spc
--     ts                       = val <$> t1s ++ t2s
--     t1s                      = [t | (x, t) <- tySigs spc, x `S.member` definedVars]
--     t2s                      = [] -- [t | (_, t) <- ctor spc                            ]
--     definedVars              = S.fromList $ defVars info
--     spc                      = spec info
--
-- okQual                       = not . any isPred . map snd . q_params
--   where
--     isPred (FApp tc _)       = tc == stringFTycon "Pred"
--     isPred _                 = False


-- TODO: rewrite using foldReft'
--------------------------------------------------------------------------------
refTypeQuals :: SEnv Sort -> SourcePos -> TCEmb TyCon -> SpecType -> [Qualifier]
--------------------------------------------------------------------------------
refTypeQuals lEnv l tce t0    = go emptySEnv t0
  where
    scrape                    = refTopQuals lEnv l tce t0
    add x t γ                 = insertSEnv x (rTypeSort tce t) γ
    goBind x t γ t'           = go (add x t γ) t'
    go γ t@(RVar _ _)         = scrape γ t
    go γ (RAllT _ t)          = go γ t
    go γ (RAllP p t)          = go (insertSEnv (pname p) (rTypeSort tce $ (pvarRType p :: RSort)) γ) t
    go γ t@(RAppTy t1 t2 _)   = go γ t1 ++ go γ t2 ++ scrape γ t
    go γ (RFun x t t' _)      = go γ t ++ goBind x t γ t'
    go γ t@(RApp c ts rs _)   = scrape γ t ++ concatMap (go γ') ts ++ goRefs c γ' rs
                                where γ' = add (rTypeValueVar t) t γ
    go γ (RAllE x t t')       = go γ t ++ goBind x t γ t'
    go γ (REx x t t')         = go γ t ++ goBind x t γ t'
    go _ _                    = []
    goRefs c g rs             = concat $ zipWith (goRef g) rs (rTyConPVs c)
    goRef _ (RProp _ (RHole _)) _ = []
    goRef g (RProp s t)  _    = go (insertsSEnv g s) t
    insertsSEnv               = foldr (\(x, t) γ -> insertSEnv x (rTypeSort tce t) γ)


refTopQuals :: (PPrint t, Reftable t, SubsTy RTyVar RSort t, Reftable (RTProp RTyCon RTyVar (UReft t)))
            => SEnv Sort
            -> SourcePos
            -> TCEmb TyCon
            -> RType RTyCon RTyVar r
            -> SEnv Sort
            -> RRType (UReft t)
            -> [Qualifier]
refTopQuals lEnv l tce t0 γ t
  = [ mkQ v so pa  | let (RR so (Reft (v, ra))) = rTypeSortedReft tce t
                   , pa                        <- conjuncts ra
                   , not $ isHole    pa
                   , not $ isGradual pa
                   , isNothing $ checkSorted (insertSEnv v so γ') pa
    ]
    ++
    [ mkP s e | let (MkUReft _ (Pr ps) _) = fromMaybe (msg t) $ stripRTypeBase t
              , p                        <- findPVar (ty_preds $ toRTypeRep t0) <$> ps
              , (s, _, e)                <- pargs p
    ]
    where
      mkQ   = mkQual  lEnv l     t0 γ
      mkP   = mkPQual lEnv l tce t0 γ
      msg t = panic Nothing $ "Qualifier.refTopQuals: no typebase" ++ showpp t
      γ'    = unionSEnv' γ lEnv

mkPQual :: (PPrint r, Reftable r, SubsTy RTyVar RSort r, Reftable (RTProp RTyCon RTyVar r))
        => SEnv Sort
        -> SourcePos
        -> TCEmb TyCon
        -> t
        -> SEnv Sort
        -> RRType r
        -> Expr
        -> Qualifier
mkPQual lEnv l tce t0 γ t e = mkQual lEnv l t0 γ' v so pa
  where
    v                      = "vv"
    so                     = rTypeSort tce t
    γ'                     = insertSEnv v so γ
    pa                     = PAtom Eq (EVar v) e

mkQual :: SEnv Sort
       -> SourcePos
       -> t
       -> SEnv Sort
       -> Symbol
       -> Sort
       -> Expr
       -> Qualifier
mkQual lEnv l _ γ v so p   = Q "Auto" ((v, so) : xts) p l
  where
    xs   = delete v $ nub $ syms p
    xts = catMaybes $ zipWith (envSort l lEnv γ) xs [0..]

envSort :: SourcePos -> SEnv Sort -> SEnv Sort -> Symbol -> Integer -> Maybe (Symbol, Sort)
envSort l lEnv tEnv x i
  | Just t <- lookupSEnv x tEnv = Just (x, t)
  | Just _ <- lookupSEnv x lEnv = Nothing
  | otherwise                   = Just (x, ai)
  where
    ai             = trace msg $ fObj $ Loc l l $ tempSymbol "LHTV" i
    msg            = "Unknown symbol in qualifier: " ++ show x
