{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE TupleSections      #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE NamedFieldPuns     #-}

{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Language.Haskell.Liquid.Types.Bounds (

    Bound(..),

    RBound, RRBound, RRBoundV,

    RBEnv, RRBEnv, RRBEnvV,

    emapBoundM,
    mapBoundTy

    ) where

import Prelude hiding (error)
import Text.PrettyPrint.HughesPJ
import GHC.Generics
import Data.Hashable
import Data.Bifunctor as Bifunctor
import Data.Data
import qualified Data.Binary         as B
import Data.Traversable
import qualified Data.HashMap.Strict as M

import qualified Language.Fixpoint.Types as F
import Language.Haskell.Liquid.Types.RefType ()
import Language.Haskell.Liquid.Types.RType
import Language.Haskell.Liquid.Types.Types


data Bound t e = Bound
  { bname   :: LocSymbol         -- ^ The name of the bound
  , tyvars  :: [t]               -- ^ Type variables that appear in the bounds
  , bparams :: [(LocSymbol, t)]  -- ^ These are abstract refinements, for now
  , bargs   :: [(LocSymbol, t)]  -- ^ These are value variables
  , bbody   :: e                 -- ^ The body of the bound
  } deriving (Data, Generic, Functor, Foldable, Traversable)
  deriving B.Binary via Generically (Bound t e)

type RBound        = RRBound RSort
type RRBound tv    = RRBoundV F.Symbol tv
type RRBoundV v tv = Bound tv (F.ExprV v)
type RBEnv         = M.HashMap LocSymbol RBound
type RRBEnv tv     = M.HashMap LocSymbol (RRBound tv)
type RRBEnvV v tv     = M.HashMap LocSymbol (RRBoundV v tv)

emapBoundM
  :: Monad m
  => ([F.Symbol] -> t0 -> m t1)
  -> ([F.Symbol] -> e0 -> m e1)
  -> Bound t0 e0
  -> m (Bound t1 e1)
emapBoundM f g b = do
    tyvars <- mapM (f []) $ tyvars b
    (e1, bparams) <- mapAccumM (\e -> fmap (e,) . traverse (f e)) [] (bparams b)
    (e2, bargs) <- mapAccumM (\e -> fmap (e,) . traverse (f e)) e1 (bargs b)
    bbody <- g e2 (bbody b)
    return b{tyvars, bparams, bargs, bbody}

mapBoundTy :: (t0 -> t1) -> Bound t0 e -> Bound t1 e
mapBoundTy f Bound{..} = do
    Bound
      { tyvars = map f tyvars
      , bparams = map (fmap f) bparams
      , bargs = map (fmap f) bargs
      , ..
      }

instance Hashable (Bound t e) where
  hashWithSalt i = hashWithSalt i . bname

instance Eq (Bound t e) where
  b1 == b2 = bname b1 == bname b2

instance (PPrint e, PPrint t) => (Show (Bound t e)) where
  show = showpp


instance (PPrint e, PPrint t) => (PPrint (Bound t e)) where
  pprintTidy k (Bound s vs ps ys e) = "bound" <+> pprintTidy k s <+>
                                      "forall" <+> pprintTidy k vs <+> "." <+>
                                      pprintTidy k (fst <$> ps) <+> "=" <+>
                                      ppBsyms k (fst <$> ys) <+> pprintTidy k e
    where
      ppBsyms _ [] = ""
      ppBsyms k' xs = "\\" <+> pprintTidy k' xs <+> "->"

instance Bifunctor Bound where
  first  f (Bound s vs ps xs e) = Bound s (f <$> vs) (fmap f <$> ps) (fmap f <$> xs) e
  second = fmap
