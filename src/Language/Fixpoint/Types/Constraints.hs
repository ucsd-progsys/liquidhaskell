{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE PatternGuards              #-}

-- | This module contains the top-level QUERY data types and elements,
--   including (Horn) implication & well-formedness constraints and sets.

module Language.Fixpoint.Types.Constraints (

   -- * Top-level Queries
    FInfo, SInfo, GInfo (..), FInfoWithOpts(..)
  , convertFormat
  , Solver

   -- * Serializing
  , toFixpoint
  , writeFInfo
  , saveQuery

   -- * Constructing Queries
  , fi

  -- * Constraints
  , WfC (..), isGWfc, updateWfCExpr
  , SubC, SubcId
  , mkSubC, subcId, sid, senv, slhs, srhs, stag, subC, wfC
  , SimpC (..)
  , Tag
  , TaggedC, clhs, crhs
  -- , strengthenLhs
  , strengthenHyp

  -- * Accessing Constraints
  , addIds
  , sinfo
  , shiftVV
  , gwInfo, GWInfo (..)

  -- * Qualifiers
  , Qualifier (..)
  , trueQual
  , qualifier
  , mkQual, remakeQual

  -- * Results
  , FixSolution
  , GFixSolution, toGFixSol
  , Result (..)
  , unsafe, isUnsafe, isSafe ,safe

  -- * Cut KVars
  , Kuts (..)
  , ksMember

  -- * Higher Order Logic
  , HOInfo (..)
  , allowHO
  , allowHOquals

  -- * Axioms
  , AxiomEnv (..)
  , Equation (..)
  , mkEquation
  , Rewrite  (..)

  -- * Misc  [should be elsewhere but here due to dependencies]
  , substVars
  ) where

import qualified Data.Binary as B
import           Data.Generics             (Data)
import           Data.Typeable             (Typeable)
import           GHC.Generics              (Generic)
import qualified Data.List                 as L -- (sort, nub, delete)
import           Data.Maybe                (catMaybes)
import           Control.DeepSeq
import           Control.Monad             (void)
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Config hiding (allowHO)
import           Language.Fixpoint.Types.Triggers
import           Language.Fixpoint.Types.Names
import           Language.Fixpoint.Types.Errors
import           Language.Fixpoint.Types.Spans
import           Language.Fixpoint.Types.Sorts
import           Language.Fixpoint.Types.Refinements
import           Language.Fixpoint.Types.Substitutions
import           Language.Fixpoint.Types.Environments
import qualified Language.Fixpoint.Utils.Files as Files

import           Language.Fixpoint.Misc
import           Text.PrettyPrint.HughesPJ
import qualified Data.HashMap.Strict       as M
import qualified Data.HashSet              as S

--------------------------------------------------------------------------------
-- | Constraints ---------------------------------------------------------------
--------------------------------------------------------------------------------

{-@ type Tag = { v : [Int] | len v == 1 } @-}

type Tag           = [Int]

data WfC a  =  WfC  { wenv  :: !IBindEnv
                    , wrft  :: (Symbol, Sort, KVar)
                    , winfo :: !a
                    }
             | GWfC { wenv  :: !IBindEnv
                    , wrft  :: !(Symbol, Sort, KVar)
                    , winfo :: !a
                    , wexpr :: !Expr
                    , wloc  :: !GradInfo
                    }
              deriving (Eq, Generic, Functor)

data GWInfo = GWInfo { gsym  :: Symbol
                     , gsort :: Sort
                     , gexpr :: Expr
                     , ginfo :: GradInfo
                     }
              deriving (Eq, Generic)

gwInfo :: WfC a -> GWInfo
gwInfo (GWfC _ (x,s,_) _ e i)
  = GWInfo x s e i
gwInfo _
  = errorstar "gwInfo"

updateWfCExpr :: (Expr -> Expr) -> WfC a -> WfC a
updateWfCExpr _ w@(WfC {})  = w
updateWfCExpr f w@(GWfC {}) = w{wexpr = f (wexpr w)}

isGWfc :: WfC a -> Bool
isGWfc (GWfC {}) = True
isGWfc (WfC  {}) = False

instance HasGradual (WfC a) where
  isGradual = isGWfc

type SubcId = Integer

data SubC a = SubC
  { _senv  :: !IBindEnv
  , slhs   :: !SortedReft
  , srhs   :: !SortedReft
  , _sid   :: !(Maybe SubcId)
  , _stag  :: !Tag
  , _sinfo :: !a
  }
  deriving (Eq, Generic, Functor)

data SimpC a = SimpC
  { _cenv  :: !IBindEnv
  , _crhs  :: !Expr
  , _cid   :: !(Maybe Integer)
  , _cbind :: !BindId               -- ^ Id of lhs/rhs binder
  , _ctag  :: !Tag
  , _cinfo :: !a
  }
  deriving (Generic, Functor)


strengthenHyp :: SInfo a -> [(Integer, Expr)] -> SInfo a
strengthenHyp si ies = strengthenBinds si bindExprs
  where
    bindExprs        = safeFromList "strengthenHyp" (mapFst (subcBind si) <$> ies)

subcBind :: SInfo a -> Integer -> BindId
subcBind si i
  | Just c <- M.lookup i (cm si)
  = _cbind c
  | otherwise
  = errorstar $ "Unknown subcId in subcBind: " ++ show i


strengthenBinds :: SInfo a -> M.HashMap BindId Expr -> SInfo a
strengthenBinds si m = si { bs = mapBindEnv f (bs si) }
  where
    f i (x, sr)      = case M.lookup i m of
                         Nothing -> (x, sr)
                         Just e  -> (x, strengthenSortedReft sr e)

strengthenSortedReft :: SortedReft -> Expr -> SortedReft
strengthenSortedReft (RR s (Reft (v, r))) e = RR s (Reft (v, pAnd [r, e]))



{-
  [(Int, Expr)]  ==> [(BindId, Expr)]

 -}

-- strengthenLhs :: Expr -> SubC a -> SubC a
-- strengthenLhs e subc = subc {slhs = go (slhs subc)}
--  where
--    go (RR s (Reft(v, r))) = RR s (Reft (v, pAnd [r, e]))

class TaggedC c a where
  senv  :: c a -> IBindEnv
  sid   :: c a -> Maybe Integer
  stag  :: c a -> Tag
  sinfo :: c a -> a
  clhs  :: BindEnv -> c a -> [(Symbol, SortedReft)]
  crhs  :: c a -> Expr

instance TaggedC SimpC a where
  senv      = _cenv
  sid       = _cid
  stag      = _ctag
  sinfo     = _cinfo
  crhs      = _crhs
  clhs be c = envCs be (senv c)

instance TaggedC SubC a where
  senv      = _senv
  sid       = _sid
  stag      = _stag
  sinfo     = _sinfo
  crhs      = reftPred . sr_reft . srhs
  clhs be c = sortedReftBind (slhs c) : envCs be (senv c)

sortedReftBind :: SortedReft -> (Symbol, SortedReft)
sortedReftBind sr = (x, sr)
  where
    Reft (x, _)   = sr_reft sr

subcId :: (TaggedC c a) => c a -> SubcId
subcId = mfromJust "subCId" . sid

---------------------------------------------------------------------------
-- | Solutions and Results
---------------------------------------------------------------------------

type GFixSolution = GFixSol Expr

type FixSolution  = M.HashMap KVar Expr
newtype GFixSol e = GSol (M.HashMap KVar (e, [e]))
  deriving (Generic, Monoid, Functor)

toGFixSol :: M.HashMap KVar (e, [e]) -> GFixSol e
toGFixSol = GSol


data Result a = Result { resStatus    :: !(FixResult a)
                       , resSolution  :: !FixSolution
                       , gresSolution :: !GFixSolution }
                deriving (Generic, Show)

instance Monoid (Result a) where
  mempty        = Result mempty mempty mempty
  mappend r1 r2 = Result stat soln gsoln
    where
      stat      = mappend (resStatus r1)    (resStatus r2)
      soln      = mappend (resSolution r1)  (resSolution r2)
      gsoln     = mappend (gresSolution r1) (gresSolution r2)

unsafe, safe :: Result a
unsafe = mempty {resStatus = Unsafe []}
safe   = mempty {resStatus = Safe}

isSafe :: Result a -> Bool
isSafe (Result Safe _ _) = True
isSafe _                 = False

isUnsafe :: Result a -> Bool
isUnsafe r | Unsafe _ <- resStatus r
  = True
isUnsafe _ = False

instance (Ord a, Fixpoint a) => Fixpoint (FixResult (SubC a)) where
  toFix Safe             = text "Safe"
  -- toFix (UnknownError d) = text $ "Unknown Error: " ++ d
  toFix (Crash xs msg)   = vcat $ [ text "Crash!" ] ++  pprSinfos "CRASH: " xs ++ [parens (text msg)]
  toFix (Unsafe xs)      = vcat $ text "Unsafe:" : pprSinfos "WARNING: " xs

pprSinfos :: (Ord a, Fixpoint a) => String -> [SubC a] -> [Doc]
pprSinfos msg = map ((text msg <>) . toFix) . L.sort . fmap sinfo

instance Fixpoint a => Show (WfC a) where
  show = showFix

instance Fixpoint a => Show (SubC a) where
  show = showFix

instance Fixpoint a => Show (SimpC a) where
  show = showFix

instance Fixpoint a => PPrint (SubC a) where
  pprintTidy _ = toFix

instance Fixpoint a => PPrint (SimpC a) where
  pprintTidy _ = toFix

instance Fixpoint a => PPrint (WfC a) where
  pprintTidy _ = toFix

instance Fixpoint a => Fixpoint (SubC a) where
  toFix c     = hang (text "\n\nconstraint:") 2 bd
     where bd =   toFix (senv c)
              $+$ text "lhs" <+> toFix (slhs c)
              $+$ text "rhs" <+> toFix (srhs c)
              $+$ (pprId (sid c) <+> text "tag" <+> toFix (stag c))
              $+$ toFixMeta (text "constraint" <+> pprId (sid c)) (toFix (sinfo c))

instance Fixpoint a => Fixpoint (SimpC a) where
  toFix c     = hang (text "\n\nsimpleConstraint:") 2 bd
     where bd =   toFix (senv c)
              $+$ text "rhs" <+> toFix (crhs c)
              $+$ (pprId (sid c) <+> text "tag" <+> toFix (stag c))
              $+$ toFixMeta (text "simpleConstraint" <+> pprId (sid c)) (toFix (sinfo c))

instance Fixpoint a => Fixpoint (WfC a) where
  toFix w     = hang (text "\n\nwf:") 2 bd
    where bd  =   toFix (wenv w)
              -- NOTE: this next line is printed this way for compatability with the OCAML solver
              $+$ text "reft" <+> toFix (RR t (Reft (v, PKVar k mempty)))
              $+$ toFixMeta (text "wf") (toFix (winfo w))
              $+$ if (isGWfc w) then (toFixMeta (text "expr") (toFix (wexpr w))) else mempty
          (v, t, k) = wrft w

toFixMeta :: Doc -> Doc -> Doc
toFixMeta k v = text "// META" <+> k <+> text ":" <+> v

pprId :: Show a => Maybe a -> Doc
pprId (Just i)  = "id" <+> tshow i
pprId _         = ""

instance PPrint GFixSolution where
  pprintTidy k (GSol xs) = vcat $ punctuate "\n\n" (pprintTidyGradual k <$> M.toList xs)

pprintTidyGradual :: Tidy -> (KVar, (Expr, [Expr])) -> Doc
pprintTidyGradual _ (x, (e, es)) = ppLocOfKVar x <+> text ":=" <+> (ppNonTauto " && " e <> pprint es)

ppLocOfKVar :: KVar -> Doc
ppLocOfKVar = text. dropWhile (/='(') . symbolString .kv

ppNonTauto :: Doc -> Expr -> Doc
ppNonTauto d e
  | isTautoPred e = mempty
  | otherwise     = pprint e <> d

instance Show   GFixSolution where
  show = showpp

----------------------------------------------------------------
instance B.Binary Qualifier
instance B.Binary Kuts
instance B.Binary HOInfo
instance B.Binary GWInfo
instance B.Binary GFixSolution
instance (B.Binary a) => B.Binary (SubC a)
instance (B.Binary a) => B.Binary (WfC a)
instance (B.Binary a) => B.Binary (SimpC a)
instance (B.Binary (c a), B.Binary a) => B.Binary (GInfo c a)

instance NFData Qualifier
instance NFData Kuts
instance NFData HOInfo
instance NFData GFixSolution
instance NFData GWInfo

instance (NFData a) => NFData (SubC a)
instance (NFData a) => NFData (WfC a)
instance (NFData a) => NFData (SimpC a)
instance (NFData (c a), NFData a) => NFData (GInfo c a)
instance (NFData a) => NFData (Result a)

---------------------------------------------------------------------------
-- | "Smart Constructors" for Constraints ---------------------------------
---------------------------------------------------------------------------

wfC :: (Fixpoint a) => IBindEnv -> SortedReft -> a -> [WfC a]
wfC be sr x = if all isEmptySubst (sus ) -- ++ gsus)
                 -- NV TO RJ This tests fails with [LT:=GHC.Types.LT][EQ:=GHC.Types.EQ][GT:=GHC.Types.GT]]
                 -- NV TO RJ looks like a resolution issue
                then [WfC be (v, sr_sort sr, k) x      | k         <- ks ]
                  ++ [GWfC be (v, sr_sort sr, k) x e i | (k, e, i) <- gs ]
                else errorstar msg
  where
    msg             = "wfKvar: malformed wfC " ++ show sr ++ "\n" ++ show (sus ++ gsus)
    Reft (v, ras)   = sr_reft sr
    (ks, sus)       = unzip $ go ras
    (gs, gsus)      = unzip $ go' ras

    go (PKVar k su) = [(k, su)]
    go (PAnd es)    = [(k, su) | PKVar k su <- es]
    go _            = []

    go' (PGrad k su i e) = [((k, e, i), su)]
    go' (PAnd es)      = concatMap go' es
    go' _              = []

mkSubC :: IBindEnv -> SortedReft -> SortedReft -> Maybe Integer -> Tag -> a -> SubC a
mkSubC = SubC

subC :: IBindEnv -> SortedReft -> SortedReft -> Maybe Integer -> Tag -> a -> [SubC a]
subC γ sr1 sr2 i y z = [SubC γ sr1' (sr2' r2') i y z | r2' <- reftConjuncts r2]
   where
     RR t1 r1          = sr1
     RR t2 r2          = sr2
     sr1'              = RR t1 $ shiftVV r1  vv'
     sr2' r2'          = RR t2 $ shiftVV r2' vv'
     vv'               = mkVV i

mkVV :: Maybe Integer -> Symbol
mkVV (Just i)  = vv $ Just i
mkVV Nothing   = vvCon

shiftVV :: Reft -> Symbol -> Reft
shiftVV r@(Reft (v, ras)) v'
   | v == v'   = r
   | otherwise = Reft (v', subst1 ras (v, EVar v'))

addIds :: [SubC a] -> [(Integer, SubC a)]
addIds = zipWith (\i c -> (i, shiftId i $ c {_sid = Just i})) [1..]
  where -- Adding shiftId to have distinct VV for SMT conversion
    shiftId i c = c { slhs = shiftSR i $ slhs c }
                    { srhs = shiftSR i $ srhs c }
    shiftSR i sr = sr { sr_reft = shiftR i $ sr_reft sr }
    shiftR i r@(Reft (v, _)) = shiftVV r (intSymbol v i)

--------------------------------------------------------------------------------
-- | Qualifiers ----------------------------------------------------------------
--------------------------------------------------------------------------------

data Qualifier = Q { qName   :: !Symbol          -- ^ Name
                   , qParams :: [(Symbol, Sort)] -- ^ Parameters
                   , qBody   :: !Expr            -- ^ Predicate
                   , qPos    :: !SourcePos       -- ^ Source Location
                   }
               deriving (Eq, Show, Data, Typeable, Generic)

trueQual :: Qualifier
trueQual = Q (symbol ("QTrue" :: String)) [] mempty (dummyPos "trueQual")

instance Loc Qualifier where
  srcSpan q = SS l l
    where
      l     = qPos q

instance Fixpoint Qualifier where
  toFix = pprQual

instance PPrint Qualifier where
  pprintTidy k q = "qualif" <+> pprintTidy k (qName q) <+> "defined at" <+> pprintTidy k (qPos q)

pprQual :: Qualifier -> Doc
pprQual (Q n xts p l) = text "qualif" <+> text (symbolString n) <> parens args <> colon <+> parens (toFix p) <+> text "//" <+> toFix l
  where
    args              = intersperse comma (toFix <$> xts)

qualifier :: SEnv Sort -> SourcePos -> SEnv Sort -> Symbol -> Sort -> Expr -> Qualifier
qualifier lEnv l γ v so p   = Q "Auto" ((v, so) : xts) p l
  where
    xs  = L.delete v $ L.nub $ syms p
    xts = catMaybes $ zipWith (envSort l lEnv γ) xs [0..]

envSort :: SourcePos -> SEnv Sort -> SEnv Sort -> Symbol -> Integer -> Maybe (Symbol, Sort)
envSort l lEnv tEnv x i
  | Just t <- lookupSEnv x tEnv = Just (x, t)
  | Just _ <- lookupSEnv x lEnv = Nothing
  | otherwise                   = Just (x, ai)
  where
    ai  = {- trace msg $ -} fObj $ Loc l l $ tempSymbol "LHTV" i
    -- msg = "unknown symbol in qualifier: " ++ show x

remakeQual :: Qualifier -> Qualifier
remakeQual q = {- traceShow msg $ -} mkQual (qName q) (qParams q) (qBody q) (qPos q)

-- | constructing qualifiers
mkQual :: Symbol -> [(Symbol, Sort)] -> Expr -> SourcePos -> Qualifier
mkQual n xts p = Q n ((v, t) : yts) (subst su p)
  where
    (v, t):zts = gSorts xts
    -- yts        = first mkParam <$> zts
    yts        = zts
    su         = mkSubst $ zipWith (\(z,_) (y,_) -> (z, eVar y)) zts yts

gSorts :: [(a, Sort)] -> [(a, Sort)]
gSorts xts     = [(x, substVars su t) | (x, t) <- xts]
  where
    su         = (`zip` [0..]) . sortNub . concatMap (sortVars . snd) $ xts

substVars :: [(Symbol, Int)] -> Sort -> Sort
substVars su = mapSort' tx
  where
    tx (FObj x)
      | Just i <- lookup x su = FVar i
    tx t                      = t

sortVars :: Sort -> [Symbol]
sortVars = foldSort' go []
  where
    go b (FObj x) = x : b
    go b _        = b

-- COPIED from Visitor due to cyclic deps
mapSort' :: (Sort -> Sort) -> Sort -> Sort
mapSort' f = step
  where
    step             = go . f
    go (FFunc t1 t2) = FFunc (step t1) (step t2)
    go (FApp t1 t2)  = FApp (step t1) (step t2)
    go (FAbs i t)    = FAbs i (step t)
    go t             = t

-- COPIED from Visitor due to cyclic deps
foldSort' :: (a -> Sort -> a) -> a -> Sort -> a
foldSort' f = step
  where
    step b t           = go (f b t) t
    go b (FFunc t1 t2) = L.foldl' step b [t1, t2]
    go b (FApp t1 t2)  = L.foldl' step b [t1, t2]
    go b (FAbs _ t)    = go b t
    go b _             = b


--------------------------------------------------------------------------------
-- | Constraint Cut Sets -------------------------------------------------------
--------------------------------------------------------------------------------

newtype Kuts = KS { ksVars :: S.HashSet KVar }
               deriving (Eq, Show, Generic)

instance Fixpoint Kuts where
  toFix (KS s) = vcat $ ((text "cut " <>) . toFix) <$> S.toList s

ksMember :: KVar -> Kuts -> Bool
ksMember k (KS s) = S.member k s

instance Monoid Kuts where
  mempty        = KS S.empty
  mappend k1 k2 = KS $ S.union (ksVars k1) (ksVars k2)

------------------------------------------------------------------------
-- | Constructing Queries
------------------------------------------------------------------------
fi :: [SubC a]
   -> [WfC a]
   -> BindEnv
   -> SEnv Sort
   -> SEnv Sort
   -> Kuts
   -> [Qualifier]
   -> M.HashMap BindId a
   -> Bool
   -> Bool
   -> [Triggered Expr]
   -> AxiomEnv
   -> [DataDecl]
   -> GInfo SubC a
fi cs ws binds ls ds ks qs bi aHO aHOq es axe adts
  = FI { cm       = M.fromList $ addIds cs
       , ws       = M.fromListWith err [(k, w) | w <- ws, let (_, _, k) = wrft w]
       , bs       = binds
       , gLits    = ls
       , dLits    = ds
       , kuts     = ks
       , quals    = qs
       , bindInfo = bi
       , hoInfo   = HOI aHO aHOq
       , asserts  = es
       , ae       = axe
       , ddecls   = adts
       }
  where
    --TODO handle duplicates gracefully instead (merge envs by intersect?)
    err = errorstar "multiple WfCs with same kvar"

------------------------------------------------------------------------
-- | Top-level Queries
------------------------------------------------------------------------

data FInfoWithOpts a = FIO {fioFI :: FInfo a, fioOpts :: [String]}

type FInfo a   = GInfo SubC a
type SInfo a   = GInfo SimpC a

data HOInfo = HOI { hoBinds :: Bool          -- ^ Allow higher order binds in the environemnt
                  , hoQuals :: Bool          -- ^ Allow higher order quals
                  }
  deriving (Eq, Show, Generic)

allowHO, allowHOquals :: GInfo c a -> Bool
allowHO      = hoBinds . hoInfo
allowHOquals = hoQuals . hoInfo

data GInfo c a =
  FI { cm       :: !(M.HashMap SubcId (c a))  -- ^ cst id |-> Horn Constraint
     , ws       :: !(M.HashMap KVar (WfC a))  -- ^ Kvar  |-> WfC defining its scope/args
     , bs       :: !BindEnv                   -- ^ Bind  |-> (Symbol, SortedReft)
     , gLits    :: !(SEnv Sort)               -- ^ Global Constant symbols
     , dLits    :: !(SEnv Sort)               -- ^ Distinct Constant symbols
     , kuts     :: !Kuts                      -- ^ Set of KVars *not* to eliminate
     , quals    :: ![Qualifier]               -- ^ Abstract domain
     , bindInfo :: !(M.HashMap BindId a)      -- ^ Metadata about binders
     , ddecls   :: ![DataDecl]                -- ^ User-defined data declarations
     , hoInfo   :: !HOInfo                    -- ^ Higher Order info
     , asserts  :: ![Triggered Expr]
     , ae       :: AxiomEnv
     }
  deriving (Eq, Show, Functor, Generic)

instance HasGradual (GInfo c a) where
  isGradual info = any isGradual (M.elems $ ws info)

instance Monoid HOInfo where
  mempty        = HOI False False
  mappend i1 i2 = HOI { hoBinds = hoBinds i1 || hoBinds i2
                      , hoQuals = hoQuals i1 || hoQuals i2
                      }

instance Monoid (GInfo c a) where
  mempty        = FI M.empty mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty
  mappend i1 i2 = FI { cm       = mappend (cm i1)       (cm i2)
                     , ws       = mappend (ws i1)       (ws i2)
                     , bs       = mappend (bs i1)       (bs i2)
                     , gLits    = mappend (gLits i1)    (gLits i2)
                     , dLits    = mappend (dLits i1)    (dLits i2)
                     , kuts     = mappend (kuts i1)     (kuts i2)
                     , quals    = mappend (quals i1)    (quals i2)
                     , bindInfo = mappend (bindInfo i1) (bindInfo i2)
                     , ddecls   = mappend (ddecls i1)   (ddecls i2)
                     , hoInfo   = mappend (hoInfo i1)   (hoInfo i2)
                     , asserts  = mappend (asserts i1)  (asserts i2)
                     , ae       = mappend (ae i1)       (ae i2)
                     }

instance PTable (SInfo a) where
  ptable z = DocTable [ (text "# Sub Constraints", pprint $ length $ cm z)
                      , (text "# WF  Constraints", pprint $ length $ ws z)
                      ]

--------------------------------------------------------------------------
-- | Rendering Queries
--------------------------------------------------------------------------
toFixpoint :: (Fixpoint a, Fixpoint (c a)) => Config -> GInfo c a -> Doc
--------------------------------------------------------------------------
toFixpoint cfg x' =    cfgDoc   cfg
                  $++$ declsDoc x'
                  $++$ aeDoc    x'
                  $++$ qualsDoc x'
                  $++$ kutsDoc  x'
                --   $++$ packsDoc x'
                  $++$ gConDoc   x'
                  $++$ dConDoc   x'
                  $++$ bindsDoc x'
                  $++$ csDoc    x'
                  $++$ wsDoc    x'
                  $++$ binfoDoc x'
                  $++$ text "\n"
  where
    cfgDoc cfg    = text ("// " ++ show cfg)
    gConDoc       = sEnvDoc "constant"             . gLits
    dConDoc       = sEnvDoc "distinct"             . dLits
    csDoc         = vcat     . map toFix . M.elems . cm
    wsDoc         = vcat     . map toFix . M.elems . ws
    kutsDoc       = toFix    . kuts
    -- packsDoc      = toFix    . packs
    declsDoc      = vcat     . map ((text "data" <+>) . toFix) . ddecls
    bindsDoc      = toFix    . bs
    qualsDoc      = vcat     . map toFix . quals
    aeDoc         = toFix    . ae
    metaDoc (i,d) = toFixMeta (text "bind" <+> toFix i) (toFix d)
    mdata         = metadata cfg
    binfoDoc
      | mdata     = vcat     . map metaDoc . M.toList . bindInfo
      | otherwise = \_ -> text "\n"

($++$) :: Doc -> Doc -> Doc
x $++$ y = x $+$ text "\n" $+$ y

sEnvDoc :: Doc -> SEnv Sort -> Doc
sEnvDoc d       = vcat . map kvD . toListSEnv
  where
    kvD (c, so) = d <+> toFix c <+> ":" <+> parens (toFix so)

writeFInfo :: (Fixpoint a, Fixpoint (c a)) => Config -> GInfo c a -> FilePath -> IO ()
writeFInfo cfg fq f = writeFile f (render $ toFixpoint cfg fq)

--------------------------------------------------------------------------------
-- | Query Conversions: FInfo to SInfo
--------------------------------------------------------------------------------
convertFormat :: (Fixpoint a) => FInfo a -> SInfo a
--------------------------------------------------------------------------------
convertFormat fi = fi' { cm = subcToSimpc bindm <$> cm fi' }
  where
    (bindm, fi') = M.foldlWithKey' outVV (M.empty, fi) $ cm fi

subcToSimpc :: BindM -> SubC a -> SimpC a
subcToSimpc m s = SimpC
  { _cenv       = senv s
  , _crhs       = reftPred $ sr_reft $ srhs s
  , _cid        = sid s
  , _cbind      = safeLookup "subcToSimpc" (subcId s) m
  , _ctag       = stag s
  , _cinfo      = sinfo s
  }

outVV :: (BindM, FInfo a) -> Integer -> SubC a -> (BindM, FInfo a)
outVV (m, fi) i c = (m', fi')
  where
    fi'           = fi { bs = be', cm = cm' }
    m'            = M.insert i bId m
    (bId, be')    = insertBindEnv x sr $ bs fi
    cm'           = M.insert i c' $ cm fi
    c'            = c { _senv = insertsIBindEnv [bId] $ senv c }
    sr            = slhs c
    x             = reftBind $ sr_reft sr

type BindM = M.HashMap Integer BindId

---------------------------------------------------------------------------
-- | Top level Solvers ----------------------------------------------------
---------------------------------------------------------------------------
type Solver a = Config -> FInfo a -> IO (Result (Integer, a))

--------------------------------------------------------------------------------
saveQuery :: Config -> FInfo a -> IO ()
--------------------------------------------------------------------------------
saveQuery cfg fi = {- when (save cfg) $ -} do
  let fi'  = void fi
  saveBinaryQuery cfg fi'
  saveTextQuery cfg   fi'

saveBinaryQuery :: Config -> FInfo () -> IO ()
saveBinaryQuery cfg fi = do
  let bfq  = queryFile Files.BinFq cfg
  putStrLn $ "Saving Binary Query: " ++ bfq ++ "\n"
  ensurePath bfq
  B.encodeFile bfq fi

saveTextQuery :: Config -> FInfo () -> IO ()
saveTextQuery cfg fi = do
  let fq   = queryFile Files.Fq cfg
  putStrLn $ "Saving Text Query: "   ++ fq ++ "\n"
  ensurePath fq
  writeFile fq $ render (toFixpoint cfg fi)

---------------------------------------------------------------------------
-- | Axiom Instantiation Information --------------------------------------
---------------------------------------------------------------------------
data AxiomEnv = AEnv
  { aenvEqs     :: ![Equation]
  , aenvSimpl   :: ![Rewrite]
  , aenvExpand  :: M.HashMap SubcId Bool
  }
  deriving (Eq, Show, Generic)

instance B.Binary AxiomEnv
instance B.Binary Rewrite
instance B.Binary Equation
instance B.Binary SMTSolver
instance B.Binary Eliminate
instance NFData AxiomEnv
instance NFData Rewrite
instance NFData Equation
instance NFData SMTSolver
instance NFData Eliminate

instance Monoid AxiomEnv where
  mempty           = AEnv [] [] (M.fromList [])
  mappend a1 a2    = AEnv aenvEqs' aenvSimpl' aenvExpand'
    where
      aenvEqs'     = mappend (aenvEqs a1) (aenvEqs a2)
      aenvSimpl'   = mappend (aenvSimpl a1) (aenvSimpl a2)
      aenvExpand'  = mappend (aenvExpand a1) (aenvExpand a2)

instance PPrint AxiomEnv where
  pprintTidy _ = text . show

data Equation = Equ
  { eqName :: !Symbol           -- ^ name of reflected function
  , eqArgs :: [(Symbol, Sort)]  -- ^ names of parameters
  , eqBody :: !Expr             -- ^ definition of body
  , eqSort :: !Sort             -- ^ sort of body
  , eqRec  :: !Bool             -- ^ is this a recursive definition
  }
  deriving (Eq, Show, Generic)

mkEquation :: Symbol -> [(Symbol, Sort)] -> Expr -> Sort -> Equation
mkEquation f xts e out = Equ f xts e out (f `elem` syms e)

instance Subable Equation where
  syms   a = syms (eqBody a) -- ++ F.syms (axiomEq a)
  subst su = mapEqBody (subst su)
  substf f = mapEqBody (substf f)
  substa f = mapEqBody (substa f)

mapEqBody :: (Expr -> Expr) -> Equation -> Equation
mapEqBody f a = a { eqBody = f (eqBody a) }

instance PPrint Equation where
  pprintTidy _ = toFix

ppArgs :: (PPrint a) => [a] -> Doc
ppArgs = parens . intersperse ", " . fmap pprint

-- eg  SMeasure (f D [x1..xn] e)
-- for f (D x1 .. xn) = e
data Rewrite  = SMeasure
  { smName  :: Symbol         -- eg. f
  , smDC    :: Symbol         -- eg. D
  , smArgs  :: [Symbol]       -- eg. xs
  , smBody  :: Expr           -- eg. e[xs]
  }
  deriving (Eq, Show, Generic)

instance Fixpoint AxiomEnv where
  toFix axe = vcat ((toFix <$> aenvEqs axe) ++ (toFix <$> aenvSimpl axe))
              $+$ text "expand" <+> toFix (pairdoc <$> M.toList(aenvExpand axe))
    where
      pairdoc (x,y) = text $ show x ++ " : " ++ show y

instance Fixpoint Doc where
  toFix = id

instance Fixpoint Equation where
  toFix (Equ f xs e _ _) = "define" <+> toFix f <+> ppArgs xs <+> text "=" <+> parens (toFix e)

instance Fixpoint Rewrite where
  toFix (SMeasure f d xs e)
    = text "match"
   <+> toFix f
   <+> parens (toFix d <+> hsep (toFix <$> xs))
   <+> text " = "
   <+> parens (toFix e)

instance PPrint Rewrite where
  pprintTidy _ = toFix
