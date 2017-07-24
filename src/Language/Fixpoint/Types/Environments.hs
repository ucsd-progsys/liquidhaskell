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

module Language.Fixpoint.Types.Environments (

  -- * Environments
    SEnv, SESearch(..)
  , emptySEnv, toListSEnv, fromListSEnv, fromMapSEnv
  , mapSEnvWithKey, mapSEnv, mapMSEnv
  , insertSEnv, deleteSEnv, memberSEnv, lookupSEnv, unionSEnv, unionSEnv'
  , intersectWithSEnv
  , differenceSEnv
  , filterSEnv
  , lookupSEnvWithDistance
  , envCs

  -- * Local Constraint Environments
  , IBindEnv, BindId, BindMap
  , emptyIBindEnv
  , insertsIBindEnv
  , deleteIBindEnv
  , elemsIBindEnv
  , fromListIBindEnv
  , memberIBindEnv
  , unionIBindEnv
  , diffIBindEnv
  , intersectionIBindEnv
  , nullIBindEnv
  , filterIBindEnv

  -- * Global Binder Environments
  , BindEnv, beBinds
  , emptyBindEnv
  , insertBindEnv, lookupBindEnv
  , filterBindEnv, mapBindEnv, mapWithKeyMBindEnv, adjustBindEnv
  , bindEnvFromList, bindEnvToList, elemsBindEnv

  -- * Information needed to lookup and update Solutions
  , SolEnv (..)

  -- * Groups of KVars (needed by eliminate)
  , Packs (..)
  , getPack
  , makePack
  ) where

-- import qualified Data.Binary as B
import qualified Data.Binary as B
import qualified Data.List   as L
import           Data.Generics             (Data)
import           Data.Typeable             (Typeable)
import           GHC.Generics              (Generic)
import           Data.Hashable
import qualified Data.HashMap.Strict       as M
import qualified Data.HashSet              as S
import           Data.Maybe
import           Data.Function             (on)
import           Text.PrettyPrint.HughesPJ
import           Control.DeepSeq

import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Names
import           Language.Fixpoint.Types.Refinements
import           Language.Fixpoint.Types.Substitutions ()
import           Language.Fixpoint.Misc

type BindId        = Int
type BindMap a     = M.HashMap BindId a

newtype IBindEnv   = FB (S.HashSet BindId) deriving (Eq, Data, Typeable, Generic)

instance PPrint IBindEnv where
  pprintTidy _ = pprint . L.sort . elemsIBindEnv

newtype SEnv a     = SE { seBinds :: M.HashMap Symbol a }
                     deriving (Eq, Data, Typeable, Generic, Foldable, Traversable)

data SizedEnv a    = BE { _beSize  :: !Int
                        , beBinds :: !(BindMap a)
                        } deriving (Eq, Show, Functor, Foldable, Generic, Traversable)

instance PPrint a => PPrint (SizedEnv a) where
  pprintTidy k (BE _ m) = pprintTidy k m

type BindEnv       = SizedEnv (Symbol, SortedReft)
-- Invariant: All BindIds in the map are less than beSize

data SolEnv        = SolEnv { soeBinds :: !BindEnv
                            -- , soePacks :: !Packs
                            } deriving (Eq, Show, Generic)

instance PPrint a => PPrint (SEnv a) where
  pprintTidy k = pprintKVs k . L.sortBy (compare `on` fst) . toListSEnv

toListSEnv              ::  SEnv a -> [(Symbol, a)]
toListSEnv (SE env)     = M.toList env

fromListSEnv            ::  [(Symbol, a)] -> SEnv a
fromListSEnv            = SE . M.fromList

fromMapSEnv             ::  M.HashMap Symbol a -> SEnv a
fromMapSEnv             = SE

mapSEnv                 :: (a -> b) -> SEnv a -> SEnv b
mapSEnv f (SE env)      = SE (fmap f env)

mapMSEnv                :: (Monad m) => (a -> m b) -> SEnv a -> m (SEnv b)
mapMSEnv f env          = fromListSEnv <$> mapM (secondM f) (toListSEnv env)

mapSEnvWithKey          :: ((Symbol, a) -> (Symbol, b)) -> SEnv a -> SEnv b
mapSEnvWithKey f        = fromListSEnv . fmap f . toListSEnv

deleteSEnv :: Symbol -> SEnv a -> SEnv a
deleteSEnv x (SE env)   = SE (M.delete x env)

insertSEnv :: Symbol -> a -> SEnv a -> SEnv a
insertSEnv x v (SE env) = SE (M.insert x v env)

lookupSEnv :: Symbol -> SEnv a -> Maybe a
lookupSEnv x (SE env)   = M.lookup x env

emptySEnv :: SEnv a
emptySEnv               = SE M.empty

memberSEnv :: Symbol -> SEnv a -> Bool
memberSEnv x (SE env)   = M.member x env

intersectWithSEnv :: (v1 -> v2 -> a) -> SEnv v1 -> SEnv v2 -> SEnv a
intersectWithSEnv f (SE m1) (SE m2) = SE (M.intersectionWith f m1 m2)

differenceSEnv :: SEnv a -> SEnv w -> SEnv a
differenceSEnv (SE m1) (SE m2) = SE (M.difference m1 m2)

filterSEnv :: (a -> Bool) -> SEnv a -> SEnv a
filterSEnv f (SE m)     = SE (M.filter f m)

unionSEnv :: SEnv a -> M.HashMap Symbol a -> SEnv a
unionSEnv (SE m1) m2    = SE (M.union m1 m2)

unionSEnv' :: SEnv a -> SEnv a -> SEnv a
unionSEnv' (SE m1) (SE m2)    = SE (M.union m1 m2)

lookupSEnvWithDistance :: Symbol -> SEnv a -> SESearch a
lookupSEnvWithDistance x (SE env)
  = case M.lookup x env of
     Just z  -> Found z
     Nothing -> Alts $ symbol <$> alts
  where
    alts       = takeMin $ zip (editDistance x' <$> ss) ss
    ss         = symbolString <$> fst <$> M.toList env
    x'         = symbolString x
    takeMin xs = [z | (d, z) <- xs, d == getMin xs]
    getMin     = minimum . (fst <$>)


data SESearch a = Found a | Alts [Symbol]

-- | Functions for Indexed Bind Environment


instance Monoid IBindEnv where
  mempty                  = emptyIBindEnv
  mappend (FB e1) (FB e2) = FB (e1 `mappend` e2)

emptyIBindEnv :: IBindEnv
emptyIBindEnv = FB S.empty

deleteIBindEnv :: BindId -> IBindEnv -> IBindEnv
deleteIBindEnv i (FB s) = FB (S.delete i s)

memberIBindEnv :: BindId -> IBindEnv -> Bool
memberIBindEnv i (FB s) = S.member i s

insertsIBindEnv :: [BindId] -> IBindEnv -> IBindEnv
insertsIBindEnv is (FB s) = FB (foldr S.insert s is)

elemsIBindEnv :: IBindEnv -> [BindId]
elemsIBindEnv (FB s) = S.toList s

fromListIBindEnv :: [BindId] -> IBindEnv
fromListIBindEnv = FB . S.fromList

-- | Functions for Global Binder Environment
insertBindEnv :: Symbol -> SortedReft -> BindEnv -> (BindId, BindEnv)
insertBindEnv x r (BE n m) = (n, BE (n + 1) (M.insert n (x, r) m))

emptyBindEnv :: BindEnv
emptyBindEnv = BE 0 M.empty

filterBindEnv   :: (BindId -> Symbol -> SortedReft -> Bool) -> BindEnv -> BindEnv
filterBindEnv f (BE n be) = BE n (M.filterWithKey (\ n (x, r) -> f n x r) be)

bindEnvFromList :: [(BindId, Symbol, SortedReft)] -> BindEnv
bindEnvFromList [] = emptyBindEnv
bindEnvFromList bs = BE (1 + maxId) be
  where
    maxId          = maximum $ fst3 <$> bs
    be             = M.fromList [(n, (x, r)) | (n, x, r) <- bs]

elemsBindEnv :: BindEnv -> [BindId]
elemsBindEnv be = fst3 <$> bindEnvToList be

bindEnvToList :: BindEnv -> [(BindId, Symbol, SortedReft)]
bindEnvToList (BE _ be) = [(n, x, r) | (n, (x, r)) <- M.toList be]

mapBindEnv :: (BindId -> (Symbol, SortedReft) -> (Symbol, SortedReft)) -> BindEnv -> BindEnv
mapBindEnv f (BE n m) = BE n $ M.mapWithKey f m
-- (\i z -> tracepp (msg i z) $ f z) m
--  where
--    msg i z = "beMap " ++ show i ++ " " ++ show z

mapWithKeyMBindEnv :: (Monad m) => ((BindId, (Symbol, SortedReft)) -> m (BindId, (Symbol, SortedReft))) -> BindEnv -> m BindEnv
mapWithKeyMBindEnv f (BE n m) = (BE n . M.fromList) <$> mapM f (M.toList m)

lookupBindEnv :: BindId -> BindEnv -> (Symbol, SortedReft)
lookupBindEnv k (BE _ m) = fromMaybe err (M.lookup k m)
  where
    err                  = errorstar $ "lookupBindEnv: cannot find binder" ++ show k

filterIBindEnv :: (BindId -> Bool) -> IBindEnv -> IBindEnv
filterIBindEnv f (FB m) = FB (S.filter f m)

unionIBindEnv :: IBindEnv -> IBindEnv -> IBindEnv
unionIBindEnv (FB m1) (FB m2) = FB $ m1 `S.union` m2

intersectionIBindEnv :: IBindEnv -> IBindEnv -> IBindEnv
intersectionIBindEnv (FB m1) (FB m2) = FB $ m1 `S.intersection` m2

nullIBindEnv :: IBindEnv -> Bool
nullIBindEnv (FB m) = S.null m

diffIBindEnv :: IBindEnv -> IBindEnv -> IBindEnv
diffIBindEnv (FB m1) (FB m2) = FB $ m1 `S.difference` m2

adjustBindEnv :: ((Symbol, SortedReft) -> (Symbol, SortedReft)) -> BindId -> BindEnv -> BindEnv
adjustBindEnv f i (BE n m) = BE n $ M.adjust f i m

instance Functor SEnv where
  fmap = mapSEnv

instance Fixpoint BindEnv where
  toFix (BE _ m) = vcat $ map toFixBind $ hashMapToAscList m
    where
      toFixBind (i, (x, r)) = "bind" <+> toFix i <+> toFix x <+> ":" <+> toFix r

instance (Fixpoint a) => Fixpoint (SEnv a) where
   toFix (SE m)   = toFix (hashMapToAscList m)

instance Fixpoint (SEnv a) => Show (SEnv a) where
  show = render . toFix

instance Monoid (SEnv a) where
  mempty        = SE M.empty
  mappend s1 s2 = SE $ M.union (seBinds s1) (seBinds s2)

instance Monoid BindEnv where
  mempty = BE 0 M.empty
  mappend (BE 0 _) b = b
  mappend b (BE 0 _) = b
  mappend _ _        = errorstar "mappend on non-trivial BindEnvs"

envCs :: BindEnv -> IBindEnv -> [(Symbol, SortedReft)]
envCs be env = [lookupBindEnv i be | i <- elemsIBindEnv env]

instance Fixpoint (IBindEnv) where
  toFix (FB ids) = text "env" <+> toFix ids

--------------------------------------------------------------------------------

instance NFData Packs
instance NFData IBindEnv
instance NFData BindEnv
instance (NFData a) => NFData (SEnv a)

instance B.Binary Packs
instance B.Binary IBindEnv
instance B.Binary BindEnv
instance (B.Binary a) => B.Binary (SEnv a)
instance (Hashable a, Eq a, B.Binary a) => B.Binary (S.HashSet a) where
  put = B.put . S.toList
  get = S.fromList <$> B.get

--------------------------------------------------------------------------------
-- | Constraint Pack Sets ------------------------------------------------------
--------------------------------------------------------------------------------

newtype Packs = Packs { packm :: M.HashMap KVar Int }
               deriving (Eq, Show, Generic)

instance Fixpoint Packs where
  toFix (Packs m) = vcat $ (("pack" <+>) . toFix) <$> kIs
    where
      kIs = L.sortBy (compare `on` snd) . M.toList $ m

instance PPrint Packs where
  pprintTidy _ = toFix

instance Monoid Packs where
  mempty        = Packs mempty
  mappend m1 m2 = Packs $ M.union (packm m1) (packm m2)

getPack :: KVar -> Packs -> Maybe Int
getPack k (Packs m) = M.lookup k m

makePack :: [S.HashSet KVar] -> Packs
makePack kvss = Packs (M.fromList kIs)
  where
    kIs       = [ (k, i) | (i, ks) <- kPacks, k <- ks ]
    kPacks    = zip [0..] . coalesce . fmap S.toList $ kvss
