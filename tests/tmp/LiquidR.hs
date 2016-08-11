-- The following file includes several refinements that have been
-- commented out, marked with 'UNCOMMENT'. As-is, running LiquidHaskell
-- on this file produces the message:
--    liquid: Prelude.head: empty list
-- The refinemnts marked with UNCOMMENT can be uncommented one-by-one,
-- each producing a different error.

{-# LANGUAGE
      Rank2Types,
      TypeFamilies,
      ExplicitForAll,
      FlexibleInstances,
      MultiParamTypeClasses,
      ConstraintKinds,
      FunctionalDependencies
 #-}

module LiquidR
  (array,
   combine,
   and,
   add,
   indexNullary,
   indexUnary,
   indexNAry) where

import Prelude ()
-- UNCOMMENT this to avoid 'Not in scope' error
-- Note that `Char` isn't used anywhere in this file.
import Data.Char
import Data.Int
import Data.Bool
import Data.Ord
import Data.Maybe

import qualified Mode

unimplemented :: a
unimplemented = unimplemented

------------------------------------------------------------------------
-- Container Types -----------------------------------------------------
------------------------------------------------------------------------

type Vector a = [a]

data Array a = Array{
    shape :: [Mode.Numeric],
    elems :: [a]
  }

{-@ type ListN a N =
      {v:[a] | (size v) = N}
@-}

{-@ measure product :: [Mode.Numeric] -> real
      product([]) = 1
      product(x:xs) = (fromJust x) * (product xs)
@-}

{-@ data Array a = Array{
      shape :: (NonEmptyList PositiveNumeric),
      elems :: (ListN a (product shape))
    }
@-}

{-@ type NonEmptyList a =
      {v:[a] | (size v) > 0}
@-}

{-@ type NonNegativeNumeric =
      {v:Mode.Numeric |
        (isJust v) =>
          (fromJust v) >= 0 }
@-}

{-@ type PositiveNumeric =
      {v:Mode.Numeric |
        (isJust v) =>
          (fromJust v) > 0 }
@-}

{-@ measure nonNegativeNumeric :: (Mode.Numeric) -> Bool @-}
nonNegativeNumeric (Just a)  = a >= 0
nonNegativeNumeric (Nothing) = True

{-@ measure nonPositiveNumeric :: (Mode.Numeric) -> Bool @-}
nonPositiveNumeric (Just a)  = a <= 0
nonPositiveNumeric (Nothing) = True

{-@ type NonPositiveNumeric =
      {v:Mode.Numeric |
        (isJust v) =>
          (fromJust v) >= 0 }
@-}

{-@ class measure allNonNegative :: (R a) -> Bool @-}
{-@ instance measure allNonNegative :: (Array a) -> Bool
  allNonNegative (Array shape elems) = allNonNegative elems
@-}

{-@ instance measure allNonNegative :: [(Mode.Numeric)] -> Bool @-}
allNonNegative ([])   = True
allNonNegative (y:ys) = (nonNegativeNumeric y) && (allNonNegative ys)

{-@ class measure allNonPositive :: (R a) -> Bool @-}
{-@ instance measure allNonPositive :: (Array a) -> Bool
  allNonPositive (Array shape elems) = allNonPositive elems
@-}
{-@ instance measure allNonPositive :: [(Mode.Numeric)] -> Bool @-}
allNonPositive ([])   = True
allNonPositive (y:ys) = (nonPositiveNumeric y) && (allNonPositive ys)

{-@ instance measure size :: [a] -> Int
    size ([])   = 0
    size (x:xs) = 1 + (size xs)
@-}

{-@ instance measure size :: (Array a) -> Int
  size (Array shape elems)   = len elems
@-}

class R m where
  type Elem m
  length :: m -> Int
  length = unimplemented

instance R (Vector a) where
  type Elem (Vector a) = a

instance R (Array a) where
  type Elem (Array a) = a

type ROf c m = (R c, Elem c ~ m)

{-@ type RNonEmpty t m =
      {v:(R t m) | (size v) > 0}
  @-}

{-@ type RNonEmptyOf t m =
      {v:(ROf t m) | (size v) > 0}
@-}


------------------------------------------------------------------------
-- Container Constructors ----------------------------------------------
------------------------------------------------------------------------

-- Constructor for vectors
{-@ measure lsize :: [[a]] -> Int
    lsize ([])   = 0
    lsize (x:xs) = (size x) + (lsize xs)
@-}

{-@ combine ::
     ys:([[_]]) ->
     {v:([_]) | (size v) = (lsize ys)}
@-}
combine :: [[a]] ->  [a]
combine = unimplemented

-- Constructor for arrays
{- array :: forall t u m.(R t, R u, Mode.Mode m) =>
    a:(RNonEmptyOf t NonNegativeNumeric) => t ->
    b:(RNonEmptyOf u m)                  => u ->
      (Array m)
@-}
array :: forall a b m.(R a, R b, Mode.Mode m) =>
            (ROf b Mode.Numeric) => b
         -> (ROf a m) => a
         -> (Array m)
array shape elems = unimplemented


-- x = array [Just 2.0 :: Mode.Numeric] [Just 2.0 :: Mode.Numeric]

------------------------------------------------------------------------
-- Subscript -----------------------------------------------------------
------------------------------------------------------------------------
-- UNCOMMENT; Produces error:
-- > Error: Bad Type Specification
-- > LiquidR.indexNullary :: (R a, Mode b) =>
-- >                         ((R a), (~ (Elem a) b)) -> a -> {VV : [b] | size a == size VV}
-- >     Sort Error in Refinement: {VV : [m_a17t] | size a == size VV}
-- >     Unbound Symbol a
-- > Perhaps you meant: VV

{- indexNullary :: forall t m.(R t, Mode.Mode m) =>
      a:(ROf t m) => t ->
     {b:(Vector m) | (size a) = (size b) }
@-}
indexNullary :: forall t m.(R t, Mode.Mode m) =>
  (ROf t m) => t -> (Vector m)
indexNullary _ = unimplemented


class (R a, R b, Mode.Mode c, (Elem b) ~ c)
    => UnarySubscript a b c where
  indexUnary :: a -> b -> (Vector (Elem a))
  indexUnary = unimplemented

-- UNCOMMENT; produces error:
-- > liquid: <no location info>: Error: Uh oh.
-- >     This should never happen! If you are seeing this message,
-- > please submit a bug report at
-- > https://github.com/ucsd-progsys/liquidhaskell/issues
-- > with this message and the source file that caused this error.
-- >
-- > RefType.toType cannot handle: {v##0 : _ | allNonNegative a
-- >             || allNonPositive v##0}
{- instance (R t, R u, _)
      => UnarySubscript t u (Mode.Numeric) where
  indexUnary ::
    a:t ->
    b:{v:_ |
          (allNonNegative a)
       || (allNonPositive v)} ->
   {c:t | if (allNonNegative b)
          then (size c) == (size b)
          else if (allNonPositive b)
          then (size c) <= (size b)
          else false}
@-}
instance (R a, R b, (Elem b) ~ Mode.Numeric)
    => UnarySubscript a b Mode.Numeric

{- don't know how to say anything meaningful here yet -}
instance (R a, R b, (Elem b) ~ Mode.Logical)
    => UnarySubscript a b Mode.Logical


class (R a, R b) => NarySubscript a b where
  indexNAry :: (R c, Elem a ~ Elem c) => a -> [b] -> c
  indexNAry = unimplemented

instance (Mode.Mode a, R b) => NarySubscript (Array a) b



------------------------------------------------------------------------
--Binary Operations ----------------------------------------------------
------------------------------------------------------------------------

-- The length of the result of any numeric or logical binary operation
-- should be the length of the longest operand. The length of the
-- longest operand must be a multiple of the length of the shortest
-- operand. If either operand has length 0, the length of the result
-- is 0.
{-@ predicate ArithmeticResult A B C =
      if (size A) = 0 || (size B) = 0
      then (size C) = 0
      else if (size A) >= (size B)
           && (size A) mod (size B) = 0
        then (size C) = (size A)
      else if (size A) < (size B)
           && (size B) mod (size A) = 0
        then (size C) = (size B)
      else false
@-}

-- UNCOMMENT; (error omitted for brevity)
{- class (R t, R u, R v) => Addition t u v where
    add :: a:t ->
           b:u ->
          {c:v | ArithmeticResult a b c }
@-}
class (R a, R b, R c) => Addition a b c | a b -> c  where
  add  :: a -> b -> c
  add  = unimplemented

-- Container type of binop result depends on
-- container type of arguments:
--    Vector `op` Vector = Array
--    Vector `op` Array  = Array
--    Array  `op` Vector = Array
--    Array  `op` Array  = Array

instance (Mode.IntoNumeric a, Mode.IntoNumeric b)
    => Addition (Vector a) (Vector b) (Vector Mode.Numeric)

instance (Mode.IntoNumeric a, Mode.IntoNumeric b)
    => Addition (Array a) (Vector b) (Array Mode.Numeric)

instance (Mode.IntoNumeric a, Mode.IntoNumeric b)
    => Addition (Vector a) (Array b) (Array Mode.Numeric)

instance (Mode.IntoNumeric a, Mode.IntoNumeric b)
    => Addition (Array a) (Array b) (Array Mode.Numeric)

-- UNCOMMENT; produces same error as previous class annotation
{- class (R t, R u, R v) => Conjunction t u v where
    and :: a:t ->
           b:u ->
          {c:v | ArithmeticResult a b c }
@-}
class (R a, R b, R c) => Conjunction a b c | a b -> c  where
  and :: a -> b -> c
  and = unimplemented

-- Alternatively, we can use instance refinements. These produce errors
-- as well, but note that the error changes between one being
-- uncommented vs. multiple being uncommented.
-- UNCOMMENT;
{-@ instance (Mode.IntoLogical t, Mode.IntoLogical u)
    => Conjunction (Vector t) (Vector u) (Vector Mode.Logical) where
    and :: a:(Vector t) ->
           b:(Vector u) ->
          {c:(Vector Mode.Logical) | ArithmeticResult a b c }
@-}
instance (Mode.IntoLogical a, Mode.IntoLogical b)
    => Conjunction (Vector a) (Vector b) (Vector Mode.Logical)
-- UNCOMMENT;
{- instance (Mode.IntoLogical t, Mode.IntoLogical u)
    => Conjunction (Array t) (Vector u) (Array Mode.Logical) where
    and :: a:(Array t) ->
           b:(Vector u) ->
          {c:(Array Mode.Logical) | ArithmeticResult a b c }
@-}
instance (Mode.IntoLogical a, Mode.IntoLogical b)
    => Conjunction (Array a) (Vector b) (Array Mode.Logical)

instance (Mode.IntoLogical a, Mode.IntoLogical b)
    => Conjunction (Vector a) (Array b) (Array Mode.Logical)

instance (Mode.IntoLogical a, Mode.IntoLogical b)
    => Conjunction (Array a) (Array b) (Array Mode.Logical)

-- and so on...
