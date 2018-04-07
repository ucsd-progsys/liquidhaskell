{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Fixpoint.Congruence.Types 
  ( -- * Queries 
    CongQuery (..)
  , Equality (..)
  , Disequality (..)
    
    -- * Terms 
  , Term 
  , identity 

    -- * Constructors
  , app
  , var
  ) where

import Data.Function (on)
import Data.Hashable
import Data.Interned

import qualified Language.Fixpoint.Types as F 

-- 1.  x = y => f x = f y
-- 2.  f(f(f(x))) = x => f(f(f(f(f(x))))) = x => f(x) = a 

_examples = [t1, t2]
  where 
    t1   = app "f" [var "x", var "y"] 
    t2   = app "f" [var "x", var "y"] 

data CongQuery   = Query [Equality] [Disequality]  
data Equality    = Eq    Term Term
data Disequality = Diseq Term Term

--------------------------------------------------------------------------------
-- | Exported Constructors
--------------------------------------------------------------------------------
app :: F.Symbol -> [Term] -> Term
app f as = intern (BApp f as)

var :: F.Symbol -> Term
var x = intern (BVar x)

--------------------------------------------------------------------------------
-- | Hash-consed Term DataType
--------------------------------------------------------------------------------
data Term 
  = Var   {-# UNPACK #-} !Id !F.Symbol 
  | App   {-# UNPACK #-} !Id !F.Symbol [Term]
--------------------------------------------------------------------------------

data UninternedTerm
  = BVar !F.Symbol 
  | BApp !F.Symbol [Term] 

instance Interned Term where
  type Uninterned Term  = UninternedTerm
  data Description Term = DVar F.Symbol
                        | DApp F.Symbol [Id]
                          deriving Show
  describe (BApp f as)  = DApp f (identity <$> as) 
  describe (BVar x)     = DVar x
  identify i            = go 
    where
      go (BApp f as)    = App i f as
      go (BVar x)       = Var i x

  cache = termCache

identity :: Term -> Id
identity (App i _ _)   = i
identity (Var i _)     = i

instance Uninternable Term where
  unintern (App _ f as)  = BApp f as
  unintern (Var _ x)     = BVar x

termCache :: Cache Term
termCache = mkCache
{-# NOINLINE termCache #-}

instance Eq (Description Term) where
  DApp f as    == DApp f' as'    = f == f' && as == as'
  DVar x       == DVar x'       = x == x'
  _            == _             = False

instance Hashable (Description Term) where
  hashWithSalt s (DApp f a)   = s `hashWithSalt` (0 :: Int) `hashWithSalt` f `hashWithSalt` a
  hashWithSalt s (DVar n)     = s `hashWithSalt` (3 :: Int) `hashWithSalt` n

instance Eq Term where
  (==) = (==) `on` identity

instance Ord Term where
  compare = compare `on` identity

