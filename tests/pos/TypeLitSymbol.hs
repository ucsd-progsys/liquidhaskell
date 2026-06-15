{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE StandaloneKindSignatures #-}

-- | Tests for data types parameterized by Symbol with LH refinements.
--
-- Exercises:
--   * Data type with a Symbol type parameter and refined field
--   * Type synonyms for Symbol literals (expanded by GHC before LH sees them)
--   * Pattern matching extracting the refined field
module TypeLitSymbol where

import Data.Kind (Type)
import GHC.TypeLits (Symbol)

-- ---------------------------------------------------------------------------
-- Type synonyms for Symbol literals.
-- ---------------------------------------------------------------------------

type Greeting :: Symbol
type Greeting = "hello"

type Farewell :: Symbol
type Farewell = "bye"

-- ---------------------------------------------------------------------------
-- ExactSym: stores a string equal to its Symbol parameter.
-- ---------------------------------------------------------------------------

{-@ data ExactSym s = ExactSym { symVal :: {v : String | v == s} } @-}
type ExactSym :: Symbol -> Type
data ExactSym (s :: Symbol) = ExactSym { symVal :: String }

-- Constructing with a literal type parameter.
mkExactHello :: ExactSym "hello"
mkExactHello = ExactSym "hello"

mkExactBye :: ExactSym "bye"
mkExactBye = ExactSym "bye"

-- Using type synonyms: GHC expands Greeting to "hello" before LH sees it.
mkExactGreeting :: ExactSym Greeting
mkExactGreeting = ExactSym "hello"

mkExactFarewell :: ExactSym Farewell
mkExactFarewell = ExactSym "bye"

-- Pattern matching on ExactSym extracts the refined value.
getGreeting :: ExactSym Greeting -> String
getGreeting (ExactSym s) = s

getFarewell :: ExactSym Farewell -> String
getFarewell (ExactSym s) = s
