-- | Expression aliases comprise @predicate@, @inline@ and @define@ annotations.
-- Here we give some contrived example specifications to test that their names
-- are resolved as expected.
-- Note that inlines and defines need the function they lift into the logic to be
-- in scope and have the same /qualification/ constraints.
-- Predicates use a different mechanism to manage qualification, but adhere
-- to the import aliases as well.
-- Also, precedence is given to locally defined (non-reflected) logic names.
module QualifiedPredAliases
  ( isNegative,
    successor,
    SetS,
    emptySetS,
    addToEmptySetS,
    singletonSetS,
  )
where

-- Both imported modules export the same names, differing in the definition of the
-- 'InSomeRange' predicate alias. When predicate names match, the lexicographic
-- last gets stored in the lifted spec.
-- See @TransitivePredAliases@.
import ExprAliases
import qualified ExprAliasesCopycat as Copy

-- * A locally defined and used predicate

{-@ predicate DiffBound X Y Z = abs (X - Y) <= abs Z @-}

{-@ translate :: n:Int -> p:(Int,Int) ->
               { p':(Int,Int) | DiffBound (fst p') (snd p') (fst p - snd p) } @-}
translate :: Int -> (Int,Int) -> (Int,Int)
translate n (x,y) = (x + n, y + n)

-- * Locally defined aliases take precedence over imported ones, meaning we don't
-- need to qualify its name when matching names from dependencies are in scope.

{-@ predicate LessThanSomeNum X = X < 10 @-}

{-@ seven :: { n:Integer | LessThanSomeNum n }@-}
seven :: Integer
seven = 7

{-@ seven' :: { n:Integer | not ( ExprAliases.LessThanSomeNum n) }@-}
seven' :: Integer
seven' = 7

-- * Qualifying predicates

-- Qualified use.
-- Note this /one/ fails verification if 'Copy.InSomeRange' is used.
{-@ one :: {z:Int | ExprAliases.InSomeRange z}@-}
one :: Int
one = 1

-- Unqualified use.
{-@ two :: {z:Int | InSomeRange z}@-}
two :: Int
two = 2

-- We need to use the import alias here to use the intended predicate alias.
{-@ eleven :: {z:Int | Copy.InSomeRange z}@-}
eleven :: Int
eleven = 11

-- It might be good to notice that once lifted, inlines and defines are not /tied/
-- to their corresponding functions. It is only required for them to be in scope.

{-@ twoStep :: n:Int -> { v:Int | v = n + 2 && v = Copy.successor (successor n) } @-}
twoStep :: Int -> Int
twoStep = successor . successor

{-@ twoStep' :: n:Int -> { v:Int | v = n + 2 && v = successor (Copy.successor n) } @-}
twoStep' :: Int -> Int
twoStep' = Copy.successor . Copy.successor

-- * Name spaces

-- Type alias and predicate alias do not clash.

{-@ type Negative = { v:Integer | Negative v } @-}

{-@ negPosInt :: { v:Int | v > 0 } -> Negative @-}
negPosInt :: Int -> Integer
negPosInt = negate . fromIntegral

-- Both @Negative@ (predicate alias) and 'isNegative' (define) are polymorhphic
-- and result in the same spec in the following examples.

{-@ x :: { v:Int | isNegative v }@-}
x :: Int
x = -1

{-@ x' :: { v:Integer | isNegative v }@-}
x' :: Integer
x' = -1

{-@ y :: { v:Int | Negative v }@-}
y :: Int
y = -2

{-@ y' :: { v:Integer | Negative v }@-}
y' :: Integer
y' = -2

-- * Mixing type aliases, predicate aliases, inlines and defines.

{-@ mult3 :: x:Negative -> { y:Int | isNegative y } -> { z:Int | Copy.isNegative z } ->
           { v:Int | (Copy.Negative v) && (v <= successor (x * y * z)) } @-}
mult3 :: Integer -> Int -> Int -> Int
mult3 x y z = if abs mult > 1
              then mult + 1
              else mult
  where mult = fromInteger x * y * z

-- * Using a private function (i.e. not in scope) inside a predicate alias.

{-@ singletonSetS :: n:Int -> {s:SetS | Member n s} @-}
singletonSetS :: Int -> SetS
singletonSetS n = addToEmptySetS n emptySetS

theOneSet :: SetS
theOneSet = singletonSetS 1
