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
  , WfC (..)
  , SubC, SubcId
  , mkSubC, subcId, sid, senv, slhs, srhs, stag, subC, wfC
  , SimpC (..)
  , Tag
  , TaggedC, clhs, crhs

  -- * Accessing Constraints
  , addIds
  , sinfo
  , shiftVV

  -- * Qualifiers
  , Qualifier (..)
  , qualifier
  , mkQual, remakeQual

  -- * Results
  , FixSolution
  , Result (..)

  -- * Cut KVars
  , Kuts (..)
  , ksMember

  -- * Higher Order Logic
  , HOInfo (..)
  , allowHO
  , allowHOquals

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

data WfC a  = WfC  { wenv  :: !IBindEnv
                   , wrft  :: (Symbol, Sort, KVar)
                   , winfo :: !a
                   }
              deriving (Eq, Generic, Functor)

type SubcId = Integer

data SubC a = SubC { _senv  :: !IBindEnv
                   , slhs   :: !SortedReft
                   , srhs   :: !SortedReft
                   , _sid   :: !(Maybe SubcId)
                   , _stag  :: !Tag
                   , _sinfo :: !a
                   }
              deriving (Eq, Generic, Functor)

data SimpC a = SimpC { _cenv  :: !IBindEnv
                     , _crhs  :: !Expr
                     , _cid   :: !(Maybe Integer)
                     , _ctag  :: !Tag
                     , _cinfo :: !a
                     }
              deriving (Generic, Functor)

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

type FixSolution = M.HashMap KVar Expr

data Result a = Result { resStatus   :: !(FixResult a)
                       , resSolution :: !FixSolution }
                deriving (Generic, Show)

instance Monoid (Result a) where
  mempty        = Result mempty mempty
  mappend r1 r2 = Result stat soln
    where
      stat      = mappend (resStatus r1)   (resStatus r2)
      soln      = mappend (resSolution r1) (resSolution r2)

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
          (v, t, k) = wrft w

toFixMeta :: Doc -> Doc -> Doc
toFixMeta k v = text "// META" <+> k <+> text ":" <+> v

pprId :: Show a => Maybe a -> Doc
pprId (Just i)  = "id" <+> tshow i
pprId _         = ""

----------------------------------------------------------------
instance B.Binary Qualifier
instance B.Binary Kuts
instance B.Binary HOInfo
instance (B.Binary a) => B.Binary (SubC a)
instance (B.Binary a) => B.Binary (WfC a)
instance (B.Binary a) => B.Binary (SimpC a)
instance (B.Binary (c a), B.Binary a) => B.Binary (GInfo c a)

instance NFData Qualifier
instance NFData Kuts
instance NFData HOInfo

instance (NFData a) => NFData (SubC a)
instance (NFData a) => NFData (WfC a)
instance (NFData a) => NFData (SimpC a)
instance (NFData (c a), NFData a) => NFData (GInfo c a)
instance (NFData a) => NFData (Result a)

---------------------------------------------------------------------------
-- | "Smart Constructors" for Constraints ---------------------------------
---------------------------------------------------------------------------

wfC :: (Fixpoint a) => IBindEnv -> SortedReft -> a -> [WfC a]
wfC be sr x = if all isEmptySubst sus
                then [WfC be (v, sr_sort sr, k) x | k <- ks]
                else errorstar msg
  where
    msg             = "wfKvar: malformed wfC " ++ show sr
    Reft (v, ras)   = sr_reft sr
    (ks, sus)       = unzip $ go ras

    go (PKVar k su) = [(k, su)]
    go (PAnd es)    = [(k, su) | PKVar k su <- es]
    go _            = []

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
   -> GInfo SubC a
fi cs ws binds ls ds ks qs bi aHO aHOq
  = FI { cm       = M.fromList $ addIds cs
       , ws       = M.fromListWith err [(k, w) | w <- ws, let (_, _, k) = wrft w]
       , bs       = binds
       , gLits    = ls
       , dLits    = ds
       , kuts     = ks
       , quals    = qs
       , bindInfo = bi
       , hoInfo   = HOI aHO aHOq
       , asserts  = mempty
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
  FI { cm       :: !(M.HashMap SubcId (c a)) -- ^ cst id |-> Horn Constraint
     , ws       :: !(M.HashMap KVar (WfC a))  -- ^ Kvar  |-> WfC defining its scope/args
     , bs       :: !BindEnv                   -- ^ Bind  |-> (Symbol, SortedReft)
     , gLits    :: !(SEnv Sort)               -- ^ Global Constant symbols
     , dLits    :: !(SEnv Sort)               -- ^ Distinct Constant symbols
     , kuts     :: !Kuts                      -- ^ Set of KVars *not* to eliminate
  --    , packs    :: !Packs                     -- ^ Pack-sets of related KVars
     , quals    :: ![Qualifier]               -- ^ Abstract domain
     , bindInfo :: !(M.HashMap BindId a)      -- ^ Metadata about binders
     , hoInfo   :: !HOInfo                    -- ^ Higher Order info
     , asserts  :: ![Expr]
     }
  deriving (Eq, Show, Functor, Generic)

instance Monoid HOInfo where
  mempty        = HOI False False
  mappend i1 i2 = HOI { hoBinds = hoBinds i1 || hoBinds i2
                      , hoQuals = hoQuals i1 || hoQuals i2
                      }

instance Monoid (GInfo c a) where
  mempty        = FI M.empty mempty mempty mempty mempty mempty mempty mempty mempty mempty
  mappend i1 i2 = FI { cm       = mappend (cm i1)       (cm i2)
                     , ws       = mappend (ws i1)       (ws i2)
                     , bs       = mappend (bs i1)       (bs i2)
                     , gLits    = mappend (gLits i1)    (gLits i2)
                     , dLits    = mappend (dLits i1)    (dLits i2)
                     , kuts     = mappend (kuts i1)     (kuts i2)
                     -- , packs    = mappend (packs i1)    (packs i2)
                     , quals    = mappend (quals i1)    (quals i2)
                     , bindInfo = mappend (bindInfo i1) (bindInfo i2)
                     , hoInfo   = mappend (hoInfo i1)   (hoInfo i2)
                     , asserts  = mappend (asserts i1)  (asserts i2)
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
toFixpoint cfg x' =    qualsDoc x'
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
    gConDoc       = sEnvDoc "constant"             . gLits
    dConDoc       = sEnvDoc "distinct"             . dLits
    csDoc         = vcat     . map toFix . M.elems . cm
    wsDoc         = vcat     . map toFix . M.elems . ws
    kutsDoc       = toFix    . kuts
    -- packsDoc      = toFix    . packs
    bindsDoc      = toFix    . bs
    qualsDoc      = vcat     . map toFix . quals
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

--------------------------------------------------------------------------
-- | Query Conversions: FInfo to SInfo
---------------------------------------------------------------------------
convertFormat :: (Fixpoint a) => FInfo a -> SInfo a
---------------------------------------------------------------------------
convertFormat fi = fi' { cm = subcToSimpc <$> cm fi' }
  where
    fi'          = M.foldlWithKey' blowOutVV fi $ cm fi

subcToSimpc :: SubC a -> SimpC a
subcToSimpc s = SimpC
  { _cenv     = senv s
  , _crhs     = reftPred $ sr_reft $ srhs s
  , _cid      = sid s
  , _ctag     = stag s
  , _cinfo    = sinfo s
  }

blowOutVV :: FInfo a -> Integer -> SubC a -> FInfo a
blowOutVV fi i subc = fi { bs = be', cm = cm' }
  where
    sr            = slhs subc
    x             = reftBind $ sr_reft sr
    (bindId, be') = insertBindEnv x sr $ bs fi
    subc'         = subc { _senv = insertsIBindEnv [bindId] $ senv subc }
    cm'           = M.insert i subc' $ cm fi


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
