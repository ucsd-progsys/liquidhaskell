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

-- | This module contains the top-level query data types and elements,
--   including (Horn) implication & well-formedness constraints and sets.

module Language.Fixpoint.Types.Constraints (

   -- * Top-level Queries
    FInfo, SInfo, GInfo (..)
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
  , SubC, mkSubC, subcId, sid, senv, slhs, srhs, stag, subC, wfC
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
  , EQual (..)
  , eQual

  -- * Results
  , FixSolution
  , Result (..)

  -- * Solutions
  , Hyp
  , Cube (..)
  , QBind
  , Cand
  , Sol (..)
  , Solution
  , solFromList, solInsert, solLookup, solResult

  -- * Cut KVars
  , Kuts (..)
  , ksMember



  ) where

import qualified Data.Binary as B
import           Data.Generics             (Data)
import           Data.Typeable             (Typeable)
import           GHC.Generics              (Generic)
import           Data.List                 (sort, nub, delete)
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

{-@ type Tag = { v : [Int] | len(v) = 1 } @-}
type Tag           = [Int]

data WfC a  = WfC  { wenv  :: !IBindEnv
                   , wrft  :: (Symbol, Sort, KVar)
                   , winfo :: !a
                   }
              deriving (Eq, Generic, Functor)

data SubC a = SubC { _senv  :: !IBindEnv
                   , slhs  :: !SortedReft
                   , srhs  :: !SortedReft
                   , _sid   :: !(Maybe Integer)
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

subcId :: (TaggedC c a) => c a -> Integer
subcId = mfromJust "subCId" . sid

---------------------------------------------------------------------------
-- | Solutions and Results
---------------------------------------------------------------------------

type FixSolution = M.HashMap KVar Expr

data Result a = Result { resStatus   :: FixResult a
                       , resSolution :: FixSolution }
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
pprSinfos msg = map ((text msg <>) . toFix) . sort . fmap sinfo

instance Fixpoint a => Show (WfC a) where
  show = showFix

instance Fixpoint a => Show (SubC a) where
  show = showFix

instance Fixpoint a => Show (SimpC a) where
  show = showFix

instance Fixpoint a => PPrint (SubC a) where
  pprint = toFix
instance Fixpoint a => PPrint (SimpC a) where
  pprint = toFix
instance Fixpoint a => PPrint (WfC a) where
  pprint = toFix

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

pprId (Just i)  = text "id" <+> tshow i
pprId _         = text ""

----------------------------------------------------------------
instance B.Binary Qualifier
instance B.Binary Kuts
instance (B.Binary a) => B.Binary (SubC a)
instance (B.Binary a) => B.Binary (WfC a)
instance (B.Binary a) => B.Binary (SimpC a)
instance (B.Binary (c a), B.Binary a) => B.Binary (GInfo c a)

instance NFData Qualifier
instance NFData Kuts

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

addIds = zipWith (\i c -> (i, shiftId i $ c {_sid = Just i})) [1..]
  where -- Adding shiftId to have distinct VV for SMT conversion
    shiftId i c = c { slhs = shiftSR i $ slhs c }
                    { srhs = shiftSR i $ srhs c }
    shiftSR i sr = sr { sr_reft = shiftR i $ sr_reft sr }
    shiftR i r@(Reft (v, _)) = shiftVV r (intSymbol v i)

--------------------------------------------------------------------------------
-- | Qualifiers ----------------------------------------------------------------
--------------------------------------------------------------------------------

data Qualifier = Q { q_name   :: Symbol           -- ^ Name
                   , q_params :: [(Symbol, Sort)] -- ^ Parameters
                   , q_body   :: Expr             -- ^ Predicate
                   , q_pos    :: !SourcePos       -- ^ Source Location
                   }
               deriving (Eq, Show, Data, Typeable, Generic)

instance Loc Qualifier where
  srcSpan q = SS l l
    where
      l     = q_pos q

instance Fixpoint Qualifier where
  toFix = pprQual

instance PPrint Qualifier where
  pprint q = "qualif" <+> pprint (q_name q) <+> "defined at" <+> pprint (q_pos q)


pprQual (Q n xts p l) = text "qualif" <+> text (symbolString n) <> parens args <> colon <+> parens (toFix p) <+> text "//" <+> toFix l
  where
    args              = intersperse comma (toFix <$> xts)

qualifier :: SEnv Sort -> SourcePos -> SEnv Sort -> Symbol -> Sort -> Expr -> Qualifier
qualifier lEnv l γ v so p   = Q "Auto" ((v, so) : xts) p l
  where
    xs  = delete v $ nub $ syms p
    xts = catMaybes $ zipWith (envSort l lEnv γ) xs [0..]

envSort :: SourcePos -> SEnv Sort -> SEnv Sort -> Symbol -> Integer -> Maybe (Symbol, Sort)
envSort l lEnv tEnv x i
  | Just t <- lookupSEnv x tEnv = Just (x, t)
  | Just _ <- lookupSEnv x lEnv = Nothing
  | otherwise                   = Just (x, ai)
  where
    ai  = {- trace msg $ -} fObj $ Loc l l $ tempSymbol "LHTV" i
    -- msg = "unknown symbol in qualifier: " ++ show x

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
fi cs ws binds ls ks qs bi fn aHO 
  = FI { cm       = M.fromList $ addIds cs
       , ws       = M.fromListWith err [(k, w) | w <- ws, let (_, _, k) = wrft w]
       , bs       = binds
       , lits     = ls
       , kuts     = ks
       , quals    = qs
       , bindInfo = bi
       , fileName = fn
       , allowHO  = aHO 
       }
  where
    --TODO handle duplicates gracefully instead (merge envs by intersect?)
    err = errorstar "multiple WfCs with same kvar"

------------------------------------------------------------------------
-- | Top-level Queries
------------------------------------------------------------------------

type FInfo a   = GInfo SubC a
type SInfo a   = GInfo SimpC a
data GInfo c a =
  FI { cm       :: M.HashMap Integer (c a)
     , ws       :: M.HashMap KVar (WfC a)
     , bs       :: !BindEnv
     , lits     :: !(SEnv Sort)
     , kuts     :: Kuts
     , quals    :: ![Qualifier]
     , bindInfo :: M.HashMap BindId a
     , fileName :: FilePath
     , allowHO  :: !Bool 
     }
  deriving (Eq, Show, Functor, Generic)


instance Monoid (GInfo c a) where
  mempty        = FI M.empty mempty mempty mempty mempty mempty mempty mempty False 
  mappend i1 i2 = FI { cm       = mappend (cm i1)       (cm i2)
                     , ws       = mappend (ws i1)       (ws i2)
                     , bs       = mappend (bs i1)       (bs i2)
                     , lits     = mappend (lits i1)     (lits i2)
                     , kuts     = mappend (kuts i1)     (kuts i2)
                     , quals    = mappend (quals i1)    (quals i2)
                     , bindInfo = mappend (bindInfo i1) (bindInfo i2)
                     , fileName = fileName i1
                     , allowHO  = allowHO i1 || allowHO i2 
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
                  $++$ conDoc   x'
                  $++$ bindsDoc x'
                  $++$ csDoc    x'
                  $++$ wsDoc    x'
                  $++$ binfoDoc x'
                  $++$ text "\n"
  where
    conDoc        = vcat     . map toFixConstant . toListSEnv . lits
    csDoc         = vcat     . map toFix . M.elems . cm
    wsDoc         = vcat     . map toFix . M.elems . ws
    kutsDoc       = toFix    . kuts
    bindsDoc      = toFix    . bs
    qualsDoc      = vcat     . map toFix . quals
    metaDoc (i,d) = toFixMeta (text "bind" <+> toFix i) (toFix d)
    mdata         = metadata cfg
    binfoDoc
      | mdata     = vcat     . map metaDoc . M.toList . bindInfo
      | otherwise = \_ -> text "\n"

($++$) :: Doc -> Doc -> Doc
x $++$ y = x $+$ text "\n" $+$ y

toFixConstant (c, so)
  = text "constant" <+> toFix c <+> text ":" <+> parens (toFix so)

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



--------------------------------------------------------------------------------
-- | Solutions (Instantiated Qualfiers )----------------------------------------
--------------------------------------------------------------------------------

data EQual = EQL { eqQual :: !Qualifier
                 , eqPred :: !Expr
                 , eqArgs :: ![Expr]
                 }
             deriving (Eq, Show, Data, Typeable, Generic)

instance PPrint EQual where
  pprint = pprint . eqPred

instance NFData EQual

{- EQL :: q:_ -> p:_ -> ListX F.Expr {q_params q} -> _ @-}
eQual :: Qualifier -> [Symbol] -> EQual
eQual q xs = EQL q p es
  where
    p      = subst su $  q_body q
    su     = mkSubst  $  safeZip "eQual" qxs es
    es     = eVar    <$> xs
    qxs    = fst     <$> q_params q


--------------------------------------------------------------------------------
-- | Types ---------------------------------------------------------------------
--------------------------------------------------------------------------------

type Solution = Sol QBind

data Sol a = Sol { sMap :: M.HashMap KVar a
                 , sHyp :: M.HashMap KVar Hyp
                 }

data Cube = Cube
  { cuBinds :: IBindEnv
  , cuSubst :: Subst
  }

type Hyp  = ListNE Cube

type QBind    = [EQual]

type Cand a   = [(Expr, a)]

instance Monoid (Sol a) where
  mempty        = Sol mempty mempty
  mappend s1 s2 = Sol { sMap = mappend (sMap s1) (sMap s2)
                      , sHyp = mappend (sHyp s1) (sHyp s2)
                      }

instance Functor Sol where
  fmap f (Sol s h) = Sol (f <$> s) h

instance PPrint a => PPrint (Sol a) where
  pprint = pprint . sMap

--------------------------------------------------------------------------------
solResult :: Solution -> M.HashMap KVar Expr
--------------------------------------------------------------------------------
solResult s = sMap $ (pAnd . fmap eqPred) <$> s


--------------------------------------------------------------------------------
-- | Create a Solution ---------------------------------------------------------
--------------------------------------------------------------------------------
solFromList :: [(KVar, a)] -> [(KVar, Hyp)] -> Sol a
solFromList kXs kYs = Sol (M.fromList kXs) (M.fromList kYs)

--------------------------------------------------------------------------------
-- | Read / Write Solution at KVar ---------------------------------------------
--------------------------------------------------------------------------------
solLookup :: Solution -> KVar -> QBind
--------------------------------------------------------------------------------
solLookup s k = M.lookupDefault [] k (sMap s)

--------------------------------------------------------------------------------
solInsert :: KVar -> a -> Sol a -> Sol a
--------------------------------------------------------------------------------
solInsert k qs s = s { sMap = M.insert k qs (sMap s) }

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

saveBinaryQuery cfg fi = do
  let bfq  = queryFile Files.BinFq cfg
  putStrLn $ "Saving Binary Query: " ++ bfq ++ "\n"
  ensurePath bfq
  B.encodeFile bfq fi

saveTextQuery cfg fi = do
  let fq   = queryFile Files.Fq cfg
  putStrLn $ "Saving Text Query: "   ++ fq ++ "\n"
  ensurePath fq
  writeFile fq $ render (toFixpoint cfg fi)
