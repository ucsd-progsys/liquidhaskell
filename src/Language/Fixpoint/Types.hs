{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE PatternGuards              #-}

-- | This module contains the data types, operations and
--   serialization functions for representing Fixpoint's
--   implication (i.e. subtyping) and well-formedness
--   constraints in Haskell.

module Language.Fixpoint.Types (

    module Language.Fixpoint.Types.PrettyPrint
  , module Language.Fixpoint.Types.Spans
  , module Language.Fixpoint.Types.Errors
  , module Language.Fixpoint.Types.Names
  , module Language.Fixpoint.Types.Sorts
  , module Language.Fixpoint.Types.Refinements
  , module Language.Fixpoint.Types.Substitutions

  , toFixpoint
  , writeFInfo
  , FInfo, SInfo, GInfo (..)
  , fi


  -- * Constraints
  , WfC (..)
  , SubC, subcId, sid, senv, slhs, srhs, subC, wfC
  , SimpC (..)
  , Tag
  , TaggedC, WrappedC (..), clhs, crhs

  -- * Accessing Constraints
  , envCs
  , addIds, sinfo

  -- * Solutions
  , Result (..)
  , FixResult (..)
  , FixSolution

  -- * Environments
  , SEnv, SESearch(..)
  , emptySEnv, toListSEnv, fromListSEnv
  , mapSEnvWithKey
  , insertSEnv, deleteSEnv, memberSEnv, lookupSEnv
  , intersectWithSEnv
  , filterSEnv
  , lookupSEnvWithDistance

  , IBindEnv, BindId, BindMap
  , emptyIBindEnv, insertsIBindEnv, deleteIBindEnv, elemsIBindEnv

  , BindEnv, beBinds
  , insertBindEnv, emptyBindEnv, lookupBindEnv, mapBindEnv, adjustBindEnv
  , bindEnvFromList, bindEnvToList
  , unionIBindEnv

  -- * Qualifiers
  , Qualifier (..)

  -- * Cut KVars
  , Kuts (..)
  , ksEmpty
  , ksUnion
  , ksMember

  -- * FInfo to SInfo format conversion
  , convertFormat
  ) where

-- import           Debug.Trace               (trace)

import qualified Data.Binary as B
import           Data.Generics             (Data)
import           Data.Typeable             (Typeable)
import           GHC.Generics              (Generic)
import           Data.Hashable
import           Data.List                 (partition, sort)
-- import           Data.String
import           Data.Text                 (Text)
import qualified Data.Text                 as T
import           Control.DeepSeq
import           Data.Maybe                (isJust, mapMaybe, listToMaybe, fromMaybe)
import           Language.Fixpoint.Types.Config
import           Language.Fixpoint.Types.Names
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Errors
import           Language.Fixpoint.Types.Spans
import           Language.Fixpoint.Types.Sorts
import           Language.Fixpoint.Types.Refinements
import           Language.Fixpoint.Types.Substitutions
import           Language.Fixpoint.Utils.Misc
-- import           Text.Parsec.Pos
import           Text.PrettyPrint.HughesPJ

-- import           Data.Array                hiding (indices)
import qualified Data.HashMap.Strict       as M
import qualified Data.HashSet              as S

newtype Kuts = KS { ksVars :: S.HashSet KVar }
               deriving (Eq, Show, Generic)

instance Fixpoint Kuts where
  toFix (KS s) = vcat $ ((text "cut " <>) . toFix) <$> S.toList s

ksEmpty :: Kuts
ksEmpty = KS S.empty

ksUnion :: [KVar] -> Kuts -> Kuts
ksUnion kvs (KS s') = KS (S.union (S.fromList kvs) s')

ksMember :: KVar -> Kuts -> Bool
ksMember k (KS s) = S.member k s

--------------------------------------------------------------------------------
-- | Type Constructors ---------------------------------------------------------
--------------------------------------------------------------------------------

instance PTable (SInfo a) where
  ptable fi = DocTable [ (text "# Sub Constraints", pprint $ length $ cm fi)
                       , (text "# WF  Constraints", pprint $ length $ ws fi)
                       ]

---------------------------------------------------------------
-- | Environments ---------------------------------------------
---------------------------------------------------------------

toListSEnv              ::  SEnv a -> [(Symbol, a)]
toListSEnv (SE env)     = M.toList env

fromListSEnv            ::  [(Symbol, a)] -> SEnv a
fromListSEnv            = SE . M.fromList

mapSEnv f (SE env)      = SE (fmap f env)
mapSEnvWithKey f        = fromListSEnv . fmap f . toListSEnv
deleteSEnv x (SE env)   = SE (M.delete x env)
insertSEnv x y (SE env) = SE (M.insert x y env)
lookupSEnv x (SE env)   = M.lookup x env
emptySEnv               = SE M.empty
memberSEnv x (SE env)   = M.member x env
intersectWithSEnv f (SE m1) (SE m2) = SE (M.intersectionWith f m1 m2)
filterSEnv f (SE m)     = SE (M.filter f m)
lookupSEnvWithDistance x (SE env)
  = case M.lookup x env of
     Just z  -> Found z
     Nothing -> Alts $ symbol . T.pack <$> alts
  where
    alts       = takeMin $ zip (editDistance x' <$> ss) ss
    ss         = T.unpack . symbolText <$> fst <$> M.toList env
    x'         = T.unpack $ symbolText x
    takeMin xs = [z | (d, z) <- xs, d == getMin xs]
    getMin     = minimum . (fst <$>)

data SESearch a = Found a | Alts [Symbol]

-- | Functions for Indexed Bind Environment

emptyIBindEnv :: IBindEnv
emptyIBindEnv = FB S.empty

deleteIBindEnv :: BindId -> IBindEnv -> IBindEnv
deleteIBindEnv i (FB s) = FB (S.delete i s)

insertsIBindEnv :: [BindId] -> IBindEnv -> IBindEnv
insertsIBindEnv is (FB s) = FB (foldr S.insert s is)

elemsIBindEnv :: IBindEnv -> [BindId]
elemsIBindEnv (FB s) = S.toList s


-- | Functions for Global Binder Environment
insertBindEnv :: Symbol -> SortedReft -> BindEnv -> (BindId, BindEnv)
insertBindEnv x r (BE n m) = (n, BE (n + 1) (M.insert n (x, r) m))

emptyBindEnv :: BindEnv
emptyBindEnv = BE 0 M.empty

bindEnvFromList :: [(BindId, Symbol, SortedReft)] -> BindEnv
bindEnvFromList [] = emptyBindEnv
bindEnvFromList bs = BE (1 + maxId) be
  where
    maxId          = maximum $ fst3 <$> bs
    be             = M.fromList [(n, (x, r)) | (n, x, r) <- bs]

bindEnvToList :: BindEnv -> [(BindId, Symbol, SortedReft)]
bindEnvToList (BE _ be) = [(n, x, r) | (n, (x, r)) <- M.toList be]

mapBindEnv :: ((Symbol, SortedReft) -> (Symbol, SortedReft)) -> BindEnv -> BindEnv
mapBindEnv f (BE n m) = BE n $ M.map f m

lookupBindEnv :: BindId -> BindEnv -> (Symbol, SortedReft)
lookupBindEnv k (BE _ m) = fromMaybe err (M.lookup k m)
  where
    err                  = errorstar $ "lookupBindEnv: cannot find binder" ++ show k

unionIBindEnv :: IBindEnv -> IBindEnv -> IBindEnv
unionIBindEnv (FB m1) (FB m2) = FB $ m1 `S.union` m2

adjustBindEnv :: ((Symbol, SortedReft) -> (Symbol, SortedReft)) -> BindId -> BindEnv -> BindEnv
adjustBindEnv f i (BE n m) = BE n $ M.adjust f i m

instance Functor SEnv where
  fmap = mapSEnv

instance Fixpoint BindEnv where
  toFix (BE _ m) = vcat $ map toFixBind $ hashMapToAscList m

toFixBind (i, (x, r)) = text "bind" <+> toFix i <+> toFix x <+> text ":" <+> toFix r

-- instance (Fixpoint a) => Fixpoint (SEnv a) where
--   toFix (SE e)    = vcat $ map pprxt $ hashMapToAscList e
--     where
--       pprxt (x,t) = toFix x <+> colon <> colon  <+> toFix t

instance (Fixpoint a) => Fixpoint (SEnv a) where
   toFix (SE m)   = toFix (hashMapToAscList m)

instance Fixpoint (SEnv a) => Show (SEnv a) where
  show = render . toFix

-----------------------------------------------------------------------------
-- | Constraints --------------------------------------------------------------
-----------------------------------------------------------------------------

{-@ type Tag = { v : [Int] | len(v) = 1 } @-}
type Tag           = [Int]

type BindId        = Int
type BindMap a     = M.HashMap BindId a

newtype IBindEnv   = FB (S.HashSet BindId) deriving (Eq, Data, Typeable, Generic)

newtype SEnv a     = SE { seBinds :: M.HashMap Symbol a }
                     deriving (Eq, Data, Typeable, Generic, Foldable, Traversable)

data SizedEnv a    = BE { beSize  :: Int
                        , beBinds :: BindMap a
                        } deriving (Eq, Show, Functor, Foldable, Generic, Traversable)

type BindEnv       = SizedEnv (Symbol, SortedReft)
-- Invariant: All BindIds in the map are less than beSize

data SubC a = SubC { _senv  :: !IBindEnv
                   , slhs  :: !SortedReft
                   , srhs  :: !SortedReft
                   , _sid   :: !(Maybe Integer)
                   , _stag  :: !Tag
                   , _sinfo :: !a
                   }
              deriving (Eq, Generic, Functor)

data SimpC a = SimpC { _cenv  :: !IBindEnv
                     , _crhs  :: !Pred
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
  crhs  :: c a -> Pred

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

-- lhsCs, rhsCs :: SubC a -> Reft
-- lhsCs      = sr_reft . slhs
-- rhsCs      = sr_reft . srhs

data WrappedC a where
  WrapC :: (TaggedC c a, Show (c a)) => { _x :: c a } -> WrappedC a


instance Show (WrappedC a) where
  show (WrapC x) = show x

instance TaggedC WrappedC a where
  senv  (WrapC x)   = senv  x
  sid   (WrapC x)   = sid   x
  stag  (WrapC x)   = stag  x
  sinfo (WrapC x)   = sinfo x
  crhs  (WrapC x)   = crhs  x
  clhs  b (WrapC x) = clhs b x

data WfC a  = WfC  { wenv  :: !IBindEnv
                   , wrft  :: (Symbol, Sort, KVar)
                   , winfo :: !a
                   }
              deriving (Eq, Generic, Functor)

subcId :: (TaggedC c a) => c a -> Integer
subcId = mfromJust "subCId" . sid

---------------------------------------------------------------------------
-- | The output of the Solver
---------------------------------------------------------------------------
data Result a = Result { resStatus   :: FixResult (WrappedC a)
                       , resSolution :: M.HashMap KVar Pred }
                deriving (Generic, Show)
---------------------------------------------------------------------------

instance Monoid (Result a) where
  mempty        = Result mempty mempty
  mappend r1 r2 = Result stat soln
    where
      stat      = mappend (resStatus r1)   (resStatus r2)
      soln      = mappend (resSolution r1) (resSolution r2)

-- instance Functor Result where
--   fmap f (Result x y) = Result (fmap (fmap f) x) y

type FixSolution = M.HashMap KVar Pred

instance Eq a => Eq (FixResult a) where
  Crash xs _ == Crash ys _        = xs == ys
  Unsafe xs == Unsafe ys          = xs == ys
  Safe      == Safe               = True
  _         == _                  = False

instance Monoid (FixResult a) where
  mempty                          = Safe
  mappend Safe x                  = x
  mappend x Safe                  = x
  mappend _ c@(Crash _ _)         = c
  mappend c@(Crash _ _) _         = c
  mappend (Unsafe xs) (Unsafe ys) = Unsafe (xs ++ ys)
  -- mappend u@(UnknownError _) _    = u
  -- mappend _ u@(UnknownError _)    = u

instance Functor FixResult where
  fmap f (Crash xs msg)   = Crash (f <$> xs) msg
  fmap f (Unsafe xs)      = Unsafe (f <$> xs)
  fmap _ Safe             = Safe
  -- fmap _ (UnknownError d) = UnknownError d

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

instance Fixpoint (IBindEnv) where
  toFix (FB ids) = text "env" <+> toFix ids

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
             --  $+$ text "\n"

pprId (Just i)  = text "id" <+> tshow i
pprId _         = text ""


----------------------------------------------------------------
-- | Serialization ---------------------------------------------
----------------------------------------------------------------

instance (Hashable a, Eq a, B.Binary a) => B.Binary (S.HashSet a) where
  put = B.put . S.toList
  get = S.fromList <$> B.get

instance B.Binary Qualifier
instance B.Binary Kuts
instance B.Binary IBindEnv
instance B.Binary BindEnv


instance (B.Binary a) => B.Binary (SEnv a)
instance (B.Binary a) => B.Binary (SubC a)
instance (B.Binary a) => B.Binary (WfC a)
instance (B.Binary a) => B.Binary (SimpC a)
instance (B.Binary (c a), B.Binary a) => B.Binary (GInfo c a)

----------------------------------------------------------------
-- | Strictness ------------------------------------------------
----------------------------------------------------------------

instance NFData Qualifier
instance NFData Kuts
instance NFData IBindEnv
instance NFData BindEnv



instance (NFData a) => NFData (SEnv a)
instance (NFData a) => NFData (SubC a)
instance (NFData a) => NFData (WfC a)
instance (NFData a) => NFData (SimpC a)
instance (NFData (c a), NFData a) => NFData (GInfo c a)
instance (NFData a) => NFData (Result a)
instance (NFData a) => NFData (WrappedC a) where
  rnf (WrapC _) = ()

---------------------------------------------------------------------------
-------- Constraint Constructor Wrappers ----------------------------------
---------------------------------------------------------------------------

wfC :: IBindEnv -> SortedReft -> a -> [WfC a]
wfC be sr x
  | Reft (v, PKVar k su) <- sr_reft sr
              = if isEmptySubst su
                   then [WfC be (v, sr_sort sr, k) x]
                   else err
  | otherwise = []
  where
    err       = errorstar $ "wfKvar: malformed wfC " ++ show sr

subC :: IBindEnv -> SortedReft -> SortedReft -> Maybe Integer -> Tag -> a -> [SubC a]
subC γ sr1 sr2 i y z = [SubC γ sr1' (sr2' r2') i y z | r2' <- reftConjuncts r2]
   where
     RR t1 r1          = sr1
     RR t2 r2          = sr2
     sr1'              = RR t1 $ shiftVV r1  vv'
     sr2' r2'          = RR t2 $ shiftVV r2' vv'
     vv'               = mkVV i

reftConjuncts :: Reft -> [Reft]
reftConjuncts (Reft (v, ra)) = [Reft (v, ra') | ra' <- ras']
  where
    ras'                     = if null ps then ks else ((pAnd ps) : ks)
    (ks, ps)                 = partition isKvar $ refaConjuncts ra

isKvar :: Pred -> Bool
isKvar (PKVar _ _) = True
isKvar _           = False


refaConjuncts :: Pred -> [Pred]
refaConjuncts p              = [p' | p' <- conjuncts p, not $ isTautoPred p']

mkVV :: Maybe Integer -> Symbol
mkVV (Just i)  = vv $ Just i
mkVV Nothing   = vvCon

envCs :: BindEnv -> IBindEnv -> [(Symbol, SortedReft)]
envCs be env = [lookupBindEnv i be | i <- elemsIBindEnv env]

shiftVV :: Reft -> Symbol -> Reft
shiftVV r@(Reft (v, ras)) v'
   | v == v'   = r
   | otherwise = Reft (v', subst1 ras (v, EVar v'))

addIds = zipWith (\i c -> (i, shiftId i $ c {_sid = Just i})) [1..]
  where -- Adding shiftId to have distinct VV for SMT conversion
    shiftId i c = c { slhs = shiftSR i $ slhs c }
                    { srhs = shiftSR i $ srhs c }
    shiftSR i sr = sr { sr_reft = shiftR i $ sr_reft sr }
    shiftR i r@(Reft (v, _)) = shiftVV r (v `mappend` symbol (show i))


------------------------------------------------------------------------
----------------- Qualifiers -------------------------------------------
------------------------------------------------------------------------


data Qualifier = Q { q_name   :: Symbol           -- ^ Name
                   , q_params :: [(Symbol, Sort)] -- ^ Parameters
                   , q_body   :: Pred             -- ^ Predicate
                   , q_pos    :: !SourcePos       -- ^ Source Location
                   }
               deriving (Eq, Show, Data, Typeable, Generic)

instance Loc Qualifier where
  srcSpan q = SS l l
    where
      l     = q_pos q

instance Fixpoint Qualifier where
  toFix = pprQual

instance Fixpoint () where
  toFix _ = text "()"

pprQual (Q n xts p l) = text "qualif" <+> text (symbolString n) <> parens args <> colon <+> toFix p <+> text "//" <+> toFix l
  where
    args              = intersperse comma (toFix <$> xts)

------------------------------------------------------------------------
----------------- Top-Level Constraint System --------------------------
------------------------------------------------------------------------

------------------------------------------------------------------------
-- | Constructing an FInfo
------------------------------------------------------------------------
fi cs ws binds ls ks qs bi fn
  = FI { cm       = M.fromList $ addIds cs
       , ws       = M.fromListWith err [(k, w) | w <- ws, let (_, _, k) = wrft w]
       , bs       = binds
       , lits     = ls
       , kuts     = ks
       , quals    = qs
       , bindInfo = bi
       , fileName = fn
       }
  where
    --TODO handle duplicates gracefully instead (merge envs by intersect?)
    err = errorstar "multiple WfCs with same kvar"

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
     }
  deriving (Eq, Show, Functor, Generic)

instance Monoid Kuts where
  mempty        = KS S.empty
  mappend k1 k2 = KS $ S.union (ksVars k1) (ksVars k2)

instance Monoid (SEnv a) where
  mempty        = SE M.empty
  mappend s1 s2 = SE $ M.union (seBinds s1) (seBinds s2)

instance Monoid BindEnv where
  mempty = BE 0 M.empty
  mappend (BE 0 _) b = b
  mappend b (BE 0 _) = b
  mappend _ _        = errorstar "mappend on non-trivial BindEnvs"

instance Monoid (GInfo c a) where
  mempty        = FI M.empty mempty mempty mempty mempty mempty mempty mempty
  mappend i1 i2 = FI { cm       = mappend (cm i1)       (cm i2)
                     , ws       = mappend (ws i1)       (ws i2)
                     , bs       = mappend (bs i1)       (bs i2)
                     , lits     = mappend (lits i1)     (lits i2)
                     , kuts     = mappend (kuts i1)     (kuts i2)
                     , quals    = mappend (quals i1)    (quals i2)
                     , bindInfo = mappend (bindInfo i1) (bindInfo i2)
                     , fileName = fileName i1
                     }

($++$) :: Doc -> Doc -> Doc
x $++$ y = x $+$ text "\n" $+$ y

toFixpoint :: (Fixpoint a, Fixpoint (c a)) => Config -> GInfo c a -> Doc
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

toFixConstant (c, so)
  = text "constant" <+> toFix c <+> text ":" <+> parens (toFix so)

writeFInfo :: (Fixpoint a, Fixpoint (c a)) => Config -> GInfo c a -> FilePath -> IO ()
writeFInfo cfg fi f = writeFile f (render $ toFixpoint cfg fi)

-------------------------------------------------------------------------
-- | Class Predicates for Valid Refinements -----------------------------
-------------------------------------------------------------------------
---------------------------------------------------------------------------
-- | FInfo to SInfo conversion
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
