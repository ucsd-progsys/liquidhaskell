{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--prune-unsorted" @-}

-- | Tests for Haskell type synonyms and closed type families involving
-- @Symbol@, used as type arguments in LH specs.
--
-- This is the direct analog of @NatTypeSyn.hs@ for @Symbol@.
--
-- GHC expands transparent type synonyms (e.g. @Greeting@) before LH
-- processes them, so LH ultimately sees the underlying literal.  Closed
-- type families (e.g. @Greet@) are reduced by GHC during type-checking, so
-- LH sees only the reduced literal.
--
-- The test exercises:
--   * Symbol type synonyms for literals (@Greeting = \"hello\"@)
--   * Symbol type synonyms using @AppendSymbol@ (@FullGreeting = AppendSymbol ...@)
--   * Closed type families (@Greet name = AppendSymbol \"Hello, \" name@)
--   * @ConsSymbol c s@ as a type argument (prepend a Char to a Symbol)
module SymbolTypeSyn where

import Data.Kind (Type)
import GHC.TypeLits (Symbol, AppendSymbol, ConsSymbol)

-- ---------------------------------------------------------------------------
-- Type synonyms for Symbol literals.
-- ---------------------------------------------------------------------------

type Greeting :: Symbol
type Greeting = "hello"

type Farewell :: Symbol
type Farewell = "bye"

type Empty :: Symbol
type Empty = ""

-- ---------------------------------------------------------------------------
-- Type synonym using AppendSymbol (expanded by GHC before LH sees it).
-- ---------------------------------------------------------------------------

type FullGreeting :: Symbol
type FullGreeting = AppendSymbol "hello" " world"

type Prefixed :: Symbol -> Symbol
type Prefixed s = AppendSymbol "pre_" s

-- ---------------------------------------------------------------------------
-- Closed type family: reduced to a concrete Symbol literal at the call site.
-- ---------------------------------------------------------------------------

type family Greet (name :: Symbol) :: Symbol where
  Greet name = AppendSymbol "Hello, " name

-- ---------------------------------------------------------------------------
-- ExactSym: stores a string equal to its Symbol parameter.
-- ---------------------------------------------------------------------------

{-@ data ExactSym s = ExactSym { symVal :: {v : String | v == s} } @-}
type ExactSym :: Symbol -> Type
data ExactSym (s :: Symbol) = ExactSym { symVal :: String }

-- Using the Greeting synonym: expands to ExactSym "hello", field must equal "hello".
mkExactGreeting :: ExactSym Greeting
mkExactGreeting = ExactSym "hello"

-- Using the Farewell synonym: expands to ExactSym "bye".
mkExactFarewell :: ExactSym Farewell
mkExactFarewell = ExactSym "bye"

-- Using the Empty synonym: field must equal "".
mkExactEmpty :: ExactSym Empty
mkExactEmpty = ExactSym ""

-- Using the FullGreeting synonym: AppendSymbol "hello" " world" = "hello world".
mkExactFullGreeting :: ExactSym FullGreeting
mkExactFullGreeting = ExactSym "hello world"

-- Using the Prefixed synonym: Prefixed "name" = AppendSymbol "pre_" "name" = "pre_name".
mkExactPrefixedName :: ExactSym (Prefixed "name")
mkExactPrefixedName = ExactSym "pre_name"

-- Using the Greet type family: Greet "Alice" = AppendSymbol "Hello, " "Alice" = "Hello, Alice".
mkExactGreetAlice :: ExactSym (Greet "Alice")
mkExactGreetAlice = ExactSym "Hello, Alice"

-- Using ConsSymbol: ConsSymbol 'H' "ello" = "Hello".
mkExactConsH :: ExactSym (ConsSymbol 'H' "ello")
mkExactConsH = ExactSym "Hello"

-- ---------------------------------------------------------------------------
-- Pattern-match: type synonym in the function signature.
-- ---------------------------------------------------------------------------

{-@ getGreeting :: ExactSym Greeting -> {v : String | v == "hello"} @-}
getGreeting :: ExactSym Greeting -> String
getGreeting (ExactSym s) = s

-- Using FullGreeting synonym: result equals "hello world".
{-@ getFullGreeting :: ExactSym FullGreeting -> {v : String | v == "hello world"} @-}
getFullGreeting :: ExactSym FullGreeting -> String
getFullGreeting (ExactSym s) = s

-- Using Greet type family: result equals "Hello, Alice".
{-@ getGreetAlice :: ExactSym (Greet "Alice") -> {v : String | v == "Hello, Alice"} @-}
getGreetAlice :: ExactSym (Greet "Alice") -> String
getGreetAlice (ExactSym s) = s

-- Using ConsSymbol in the argument type: ConsSymbol 'H' "ello" normalises to
-- "Hello" (GHC reduces it).  The LH annotation uses a string literal "Hello"
-- directly because LH cannot yet parse ConsSymbol in spec annotations.
getConsH :: ExactSym (ConsSymbol 'H' "ello") -> String
getConsH (ExactSym s) = s
