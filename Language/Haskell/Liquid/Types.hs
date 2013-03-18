
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

  )
  where


import Data.Hashable
import Text.Parsec.Pos              (SourcePos, newPos) 
import Language.Fixpoint.Types 

data Located a = Loc { loc :: !SourcePos
                     , val :: a
                     }

type LocSymbol = Located Symbol
type LocString = Located String

dummyPos = newPos "?" 0 0 

instance Fixpoint a => Fixpoint (Located a) where
  toFix = toFix . val 

instance Symbolic a => Symbolic (Located a) where
  symbol = symbol . val 

instance Expression a => Expression (Located a) where
  expr   = expr . val

instance Functor Located where
  fmap f (Loc l x) =  Loc l (f x)

instance Show a => Show (Located a) where
  show (Loc l x) = show x ++ " defined at " ++ show l

instance Eq a => Eq (Located a) where
  (Loc _ x) == (Loc _ y) = x == y

instance Ord a => Ord (Located a) where
  compare x y = compare (val x) (val y)





instance Hashable a => Hashable (Located a) where
  hashWithSalt i = hashWithSalt i . val
