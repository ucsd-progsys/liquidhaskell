-- From Data.ByteString.Fusion

module SPair (
-- * Strict pairs and sums
    PairS(..)
  , moo
  , poo
  ) where

infixl 2 :*:

-- |Strict pair
data PairS a b = !a :*: !b deriving (Eq,Ord,Show)

{-@ qualif PSnd(v: a, x:b): v = (psnd x)                            @-}
{-@ data PairS a b <p :: x0:a -> b -> Prop> = (:*:) (x::a) (y::b)   @-}

{-@ measure pfst :: (PairS a b) -> a 
    pfst ((:*:) x y) = x 
  @-} 

{-@ measure psnd :: (PairS a b) -> b 
    psnd ((:*:) x y) = y 
  @-} 

{-@ measure tsnd :: (a, b) -> b 
    tsnd (x, y) = y 
  @-} 

{-@ type FooS a = PairS <{\z v -> v <= (psnd z)}> (PairS <{\x y -> true}> a Int) Int @-}

{-@ type Foo  a = ((a, Int), Int)<{\z v -> v <= (tsnd z)}>                           @-}

-- type TripleS a N = PairS <{\z v -> v <= (N - (psnd z))}> (PairS <{\x y -> true}> a Nat) Nat

{-@ moo :: a -> Int -> (FooS a) @-}
moo :: a -> Int -> PairS (PairS a Int) Int 
moo x n = (x :*: n :*: m)
  where
    m   = n + 1
 
{-@ poo :: a -> Int -> (Foo a)          @-}
poo     :: a -> Int -> ((a, Int), Int)
poo x n = ((x, n), m)
  where
    m   = n + 1
