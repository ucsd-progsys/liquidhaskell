
-- | This module (should) contain all the global type definitions and basic
-- instances. Need to gradually pull things into here, especially from @RefType@

module Language.Haskell.Liquid.Types (
 
  -- * Located Things
    Located (..)

  -- * Symbols
  , LocSymbol
  , LocString
  
  -- * Default unknown position
  , dummyPos

  -- * Default unknown name
  , dummyName, isDummy
  )
  where

import Control.Applicative          ((<$>))
import Data.Foldable
import Data.Hashable
import Data.Traversable
import Text.Parsec.Pos              (SourcePos, newPos) 
import Text.PrettyPrint.HughesPJ    (text)
import Language.Fixpoint.Types 

data Located a = Loc { loc :: !SourcePos
                     , val :: a
                     }

type LocSymbol = Located Symbol
type LocString = Located String

dummyName = "dummy"

isDummy :: (Show a) => a -> Bool
isDummy a = show a == dummyName

dummyPos = newPos "?" 0 0 

instance Fixpoint SourcePos where
  toFix = text . show 

instance Fixpoint a => Fixpoint (Located a) where
  toFix = toFix . val 

instance Symbolic a => Symbolic (Located a) where
  symbol = symbol . val 

instance Expression a => Expression (Located a) where
  expr   = expr . val

instance Functor Located where
  fmap f (Loc l x) =  Loc l (f x)

instance Foldable Located where
  foldMap f (Loc l x) = f x

instance Traversable Located where 
  traverse f (Loc l x) = Loc l <$> f x

instance Show a => Show (Located a) where
  show (Loc l x) = show x ++ " defined at " ++ show l

instance Eq a => Eq (Located a) where
  (Loc _ x) == (Loc _ y) = x == y

instance Ord a => Ord (Located a) where
  compare x y = compare (val x) (val y)

instance Subable a => Subable (Located a) where
  syms (Loc _ x)     = syms x
  substa f (Loc l x) = Loc l (substa f x)
  substf f (Loc l x) = Loc l (substf f x)
  subst su (Loc l x) = Loc l (subst su x)

instance Hashable a => Hashable (Located a) where
  hashWithSalt i = hashWithSalt i . val


