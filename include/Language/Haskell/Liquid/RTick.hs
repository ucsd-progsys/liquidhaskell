
--
-- Liquidate your assets: reasoning about resource usage in Liquid Haskell.
-- Martin A.T. Handley, Niki Vazou, and Graham Hutton.
--

{-@ LIQUID "--reflection" @-}

module Language.Haskell.Liquid.RTick
  (

  -- Tick datatype:
    Tick(..)
  -- Primitive resource operators:
  , fmap
  , pure
  , (<*>)
  , liftA2
  , return
  , (>>=)
  , (=<<)
  , eqBind
  , leqBind
  , geqBind
  , ap
  , liftM
  , liftM2
  -- Resource modifiers:
  , step
  , wait      -- step 1       . return
  , waitN     -- step (n > 0) . return
  , go        -- step (-1)    . return
  , goN       -- step (n < 0) . return
  , wmap      -- step 1       . fmap f
  , wmapN     -- step (n > 0) . fmap f
  , gmap      -- step (-1)    . fmap f
  , gmapN     -- step (n < 0) . fmap f
  , (</>)     -- step 1       . (f <*>)
  , (<//>)    -- step 2       . (f <*>)
  , (<\>)     -- step (-1)    . (f <*>)
  , (<\\>)    -- step (-2)    . (f <*>)
  , (>/=)     -- step 1       . (>>= f)
  , (=/<)     -- step 1       . (>>= f)
  , (>//=)    -- step 2       . (>>= f)
  , (=//<)    -- step 2       . (>>= f)
  , (>\=)     -- step (-1)    . (>>= f)
  , (=\<)     -- step (-1)    . (>>= f)
  , (>\\=)    -- step (-2)    . (>>= f)
  , (=\\<)    -- step (-2)    . (>>= f)
  -- Memoisation:
  , pay
  , zipWithM


  ) where

import Prelude hiding ( Functor(..), Applicative(..), Monad(..), (=<<) )

import qualified Control.Applicative as A
import qualified Control.Monad       as M
import qualified Data.Functor        as F

--
-- The 'Tick' datatype and its corresponding resource modifiers.
--
-- See 'ResourceModifiers.hs' for proofs that all resource modifiers
-- can be defined using 'return', '(>>=) 'and 'step'.
--

-------------------------------------------------------------------------------
-- | 'Tick' datatype for recording resource usage:
-------------------------------------------------------------------------------

{-@ data Tick a = Tick { tcost :: Int, tval :: a } @-}
data Tick a = Tick { tcost :: Int, tval :: a }

-------------------------------------------------------------------------------
-- | Primitive resource operators:
-------------------------------------------------------------------------------

instance F.Functor Tick where
  fmap = fmap

{-@ reflect fmap @-}
{-@ fmap :: f:(a -> b) -> t1:Tick a
    -> { t:Tick b | Tick (tcost t1) (f (tval t1)) == t }
@-}
fmap :: (a -> b) -> Tick a -> Tick b
fmap f (Tick m x) = Tick m (f x)

instance A.Applicative Tick where
  pure  = pure
  (<*>) = (<*>)

{-@ reflect pure @-}
{-@ pure :: x:a -> { t:Tick a | x == tval t && 0 == tcost t } @-}
pure :: a -> Tick a
pure x = Tick 0 x

{-@ reflect <*> @-}
{-@ (<*>) :: t1:Tick (a -> b) -> t2:Tick a
    -> { t:Tick b | (tval t1) (tval t2) == tval  t &&
                    tcost t1 + tcost t2 == tcost t }
@-}
infixl 4 <*>
(<*>) :: Tick (a -> b) -> Tick a -> Tick b
Tick m f <*> Tick n x = Tick (m + n) (f x)

{-@ reflect liftA2 @-}
{-@ liftA2 :: f:(a -> b -> c) -> t1:Tick a -> t2:Tick b
    -> { t:Tick c | f (tval t1) (tval t2) == tval  t &&
                      tcost t1 + tcost t2 == tcost t }
@-}
liftA2 :: (a -> b -> c) -> Tick a -> Tick b -> Tick c
liftA2 f (Tick m x) (Tick n y) = Tick (m + n) (f x y)

instance M.Monad Tick where
  return = return
  (>>=)  = (>>=)

{-@ reflect return @-}
{-@ return :: x:a -> { t:Tick a | x == tval t && 0 == tcost t } @-}
return :: a -> Tick a
return x = Tick 0 x

{-@ reflect >>= @-}
{-@ (>>=) :: t1:Tick a -> f:(a -> Tick b)
    -> { t:Tick b | tval (f (tval t1))  == tval  t &&
         tcost t1 + tcost (f (tval t1)) == tcost t }
@-}
infixl 4 >>=
(>>=) :: Tick a -> (a -> Tick b) -> Tick b
Tick m x >>= f = let Tick n y = f x in Tick (m + n) y

{-@ reflect =<< @-}
{-@ (=<<) :: f:(a -> Tick b) -> t1:Tick a
    -> { t:Tick b | tval (f (tval t1))  == tval  t &&
         tcost t1 + tcost (f (tval t1)) == tcost t }
@-}
infixl 4 =<<
(=<<) :: (a -> Tick b) -> Tick a -> Tick b
f =<< Tick m x = let Tick n y = f x in Tick (m + n) y

{-@ reflect ap @-}
{-@ ap :: t1:(Tick (a -> b)) -> t2:Tick a
    -> { t:Tick b | (tval t1) (tval t2) == tval  t &&
                    tcost t1 + tcost t2 == tcost t }
@-}
ap :: Tick (a -> b) -> Tick a -> Tick b
ap (Tick m f) (Tick n x) = Tick (m + n) (f x)

{-@ reflect liftM @-}
{-@ liftM :: f:(a -> b) -> t1:Tick a -> { t:Tick b | tcost t1 == tcost t } @-}
liftM :: (a -> b) -> Tick a -> Tick b
liftM f (Tick m x) = Tick m (f x)

{-@ reflect liftM2 @-}
{-@ liftM2 :: f:(a -> b -> c) -> t1:Tick a -> t2:Tick b
    -> { t:Tick c | f (tval t1) (tval t2) == tval  t &&
                      tcost t1 + tcost t2 == tcost t }
@-}
liftM2 :: (a -> b -> c) -> Tick a -> Tick b -> Tick c
liftM2 f (Tick m x) (Tick n y) = Tick (m + n) (f x y)

-------------------------------------------------------------------------------

{-@ reflect eqBind @-}
{-@ eqBind :: n:Int -> t1:Tick a
    -> f:(a -> { tf:Tick b | n == tcost tf })
    -> { t:Tick b | tval (f (tval t1))  == tval  t &&
                           tcost t1 + n == tcost t }
@-}
eqBind :: Int -> Tick a -> (a -> Tick b) -> Tick b
eqBind _ (Tick m x) f = let Tick n y = f x in Tick (m + n) y

{-@ reflect leqBind @-}
{-@ leqBind :: n:Int -> t1:Tick a
    -> f:(a -> { tf:Tick b | n >= tcost tf })
    -> { t:Tick b | tcost t1 + n >= tcost t }
@-}
leqBind :: Int -> Tick a -> (a -> Tick b) -> Tick b
leqBind _ (Tick m x) f = let Tick n y = f x in Tick (m + n) y

{-@ reflect geqBind @-}
{-@ geqBind :: n:Int -> t1:Tick a
    -> f:(a -> { tf:Tick b | n <= tcost tf })
    -> { t2:Tick b | tcost t1 + n <= tcost t2 }
@-}
geqBind :: Int -> Tick a -> (a -> Tick b) -> Tick b
geqBind _ (Tick m x) f = let Tick n y = f x in Tick (m + n) y

-------------------------------------------------------------------------------
-- | Resource modifiers:
-------------------------------------------------------------------------------

{-@ reflect step @-}
{-@ step :: m:Int -> t1:Tick a
    -> { t:Tick a | tval t1 == tval t && m + tcost t1 == tcost t }
@-}
step :: Int -> Tick a -> Tick a
step m (Tick n x) = Tick (m + n) x

--
-- @wait := step 1 . return@.
--
{-@ reflect wait @-}
{-@ wait :: x:a -> { t:Tick a | x == tval t && 1 == tcost t } @-}
wait :: a -> Tick a
wait x = Tick 1 x

--
-- @waitN (n > 0) := step n . return@.
--
{-@ reflect waitN @-}
{-@ waitN :: n:Nat -> x:a
    -> { t:Tick a | x == tval t && n == tcost t }
@-}
waitN :: Int -> a -> Tick a
waitN n x = Tick n x

--
-- @go := step (-1) . return@.
--
{-@ reflect go @-}
{-@ go :: x:a -> { t:Tick a | x == tval t && (-1) == tcost t } @-}
go :: a -> Tick a
go x = Tick (-1) x

--
-- @goN (n > 0) := step (-n) . return@.
--
{-@ reflect goN @-}
{-@ goN :: { n:Nat | n > 0 } -> x:a
    -> { t:Tick a | x == tval t && (-n) == tcost t }
@-}
goN :: Int -> a -> Tick a
goN n x = Tick (-n) x

--
-- @wmap f := step 1 . fmap f@.
--
{-@ reflect wmap @-}
{-@ wmap :: f:(a -> b) -> t1:Tick a
    -> { t:Tick b | Tick (1 + tcost t1) (f (tval t1)) == t }
@-}
wmap :: (a -> b) -> Tick a -> Tick b
wmap f (Tick m x) = Tick (1 + m) (f x)

--
-- @wmapN (n > 0) f := step n . fmap f@.
--
{-@ reflect wmapN @-}
{-@ wmapN :: { m:Nat | m > 0 } -> f:(a -> b) -> t1:Tick a
    -> { t:Tick b | Tick (m + tcost t1) (f (tval t1)) == t }
@-}
wmapN :: Int -> (a -> b) -> Tick a -> Tick b
wmapN m f (Tick n x) = Tick (m + n) (f x)

--
-- @gmap f := step (-1) . fmap f@.
--
{-@ reflect gmap @-}
{-@ gmap :: f:(a -> b) -> t1:Tick a
    -> { t:Tick b | Tick (tcost t1 - 1) (f (tval t1)) == t }
@-}
gmap :: (a -> b) -> Tick a -> Tick b
gmap f (Tick m x) = Tick (m - 1) (f x)

--
-- @gmapN (n > 0) f := step (-n) . fmap f@.
--
{-@ reflect gmapN @-}
{-@ gmapN :: { m:Nat | m > 0 } -> f:(a -> b) -> t1:Tick a
    -> { t:Tick b | Tick (tcost t1 - m) (f (tval t1)) == t }
@-}
gmapN :: Int -> (a -> b) -> Tick a -> Tick b
gmapN m f (Tick n x) = Tick (n - m) (f x)

--
-- \"wapp\": @(f </>) := step 1 . (f <*>)@.
--
{-@ reflect </> @-}
{-@ (</>) :: t1:(Tick (a -> b)) -> t2:Tick a
    -> { t:Tick b | (tval t1) (tval t2) == tval  t &&
                1 + tcost t1 + tcost t2 == tcost t }
@-}
infixl 4 </>
(</>) :: Tick (a -> b) -> Tick a -> Tick b
Tick m f </> Tick n x = Tick (1 + m + n) (f x)

--
-- \"wwapp\": @(f <//>) := step 2 . (f <*>)@.
--
{-@ reflect <//> @-}
{-@ (<//>) :: t1:(Tick (a -> b)) -> t2:Tick a
    -> { t:Tick b | (tval t1) (tval t2) == tval  t &&
                2 + tcost t1 + tcost t2 == tcost t }
@-}
infixl 4 <//>
(<//>) :: Tick (a -> b) -> Tick a -> Tick b
Tick m f <//> Tick n x = Tick (2 + m + n) (f x)

--
-- \"gapp\": @(f <\>) := step (-1) . (f <*>)@.
--
{-@ reflect <\> @-}
{-@ (<\>) :: t1:(Tick (a -> b)) -> t2:Tick a
    -> { t:Tick b | (tval t1) (tval t2) == tval  t &&
                tcost t1 + tcost t2 - 1 == tcost t }
@-}
infixl 4 <\>
(<\>) :: Tick (a -> b) -> Tick a -> Tick b
Tick m f <\> Tick n x = Tick (m + n - 1) (f x)

--
-- \"ggapp\": @(f <\\>) := step (-2) . (f <*>)@.
--
{-@ reflect <\\> @-}
{-@ (<\\>) :: t1:(Tick (a -> b)) -> t2:Tick a
    -> { t:Tick b | (tval t1) (tval t2) == tval  t &&
                tcost t1 + tcost t2 - 2 == tcost t }
@-}
infixl 4 <\\>
(<\\>) :: Tick (a -> b) -> Tick a -> Tick b
Tick m f <\\> Tick n x = Tick (m + n - 2) (f x)

--
-- \"wbind\": @(>/= f) := step 1 . (>>= f)@.
--
{-@ reflect >/= @-}
{-@ (>/=) :: t1:Tick a -> f:(a -> Tick b)
    -> { t:Tick b | (tval (f (tval t1))      == tval  t) &&
         (1 + tcost t1 + tcost (f (tval t1))) == tcost t }
@-}
infixl 4 >/=
(>/=) :: Tick a -> (a -> Tick b) -> Tick b
Tick m x >/= f = let Tick n y = f x in Tick (1 + m + n) y

--
-- \"wbind\": @(f =/<) := step 1 . (f =<<)@.
--
{-@ reflect =/< @-}
{-@ (=/<) :: f:(a -> Tick b) -> t1:Tick a
    -> { t:Tick b | tval (f (tval t1))      == tval  t &&
         1 + tcost t1 + tcost (f (tval t1)) == tcost t }
@-}
infixl 4 =/<
(=/<) :: (a -> Tick b) -> Tick a -> Tick b
f =/< Tick m x = let Tick n y = f x in Tick (1 + m + n) y

--
-- \"wwbind\": @(>//= f) := step 2 . (>>= f)@.
--
{-@ reflect >//= @-}
{-@ (>//=) :: t1:Tick a -> f:(a -> Tick b)
    -> { t:Tick b | tval (f (tval t1))      == tval  t &&
         2 + tcost t1 + tcost (f (tval t1)) == tcost t }
@-}
infixl 4 >//=
(>//=) :: Tick a -> (a -> Tick b) -> Tick b
Tick m x >//= f = let Tick n y = f x in Tick (2 + m + n) y

--
-- \"wwbind\": @(f =//<) := step 2 . (f =<<)@.
--
{-@ reflect =//< @-}
{-@ (=//<) :: f:(a -> Tick b) -> t1:Tick a
    -> { t:Tick b | tval (f (tval t1))      == tval  t &&
         2 + tcost t1 + tcost (f (tval t1)) == tcost t }
@-}
infixl 4 =//<
(=//<) :: (a -> Tick b) -> Tick a -> Tick b
f =//< Tick m x = let Tick n y = f x in Tick (2 + m + n) y

--
-- \"gbind\": @(>\= f) := step (-1) . (>>= f)@.
--
{-@ reflect >\= @-}
{-@ (>\=) :: t1:Tick a -> f:(a -> Tick b)
    -> { t:Tick b | tval (f (tval t1))      == tval  t &&
         tcost t1 + tcost (f (tval t1)) - 1 == tcost t }
@-}
infixl 4 >\=
(>\=) :: Tick a -> (a -> Tick b) -> Tick b
Tick m x >\= f = let Tick n y = f x in Tick (m + n - 1) y

--
-- \"gbind\": @(f =\<) := step (-1) . (f =<<)@.
--
{-@ reflect =\< @-}
{-@ (=\<) :: f:(a -> Tick b) -> t1:Tick a
    -> { t:Tick b | tval (f (tval t1))      == tval  t &&
         tcost t1 + tcost (f (tval t1)) - 1 == tcost t }
@-}
infixl 4 =\<
(=\<) :: (a -> Tick b) -> Tick a -> Tick b
f =\< Tick m x = let Tick n y = f x in Tick (m + n - 1) y

--
-- \"ggbind\": @(>\= f) := step (-2) . (>>= f)@.
--
{-@ reflect >\\= @-}
{-@ (>\\=) :: t1:Tick a -> f:(a -> Tick b)
    -> { t:Tick b | tval (f (tval t1))      == tval  t &&
         tcost t1 + tcost (f (tval t1)) - 2 == tcost t }
@-}
infixl 4 >\\=
(>\\=) :: Tick a -> (a -> Tick b) -> Tick b
Tick m x >\\= f = let Tick n y = f x in Tick (m + n - 2) y

--
-- \"ggbind\": @(f =\\<) := step (-2) . (f =<<)@.
--
{-@ reflect =\\< @-}
{-@ (=\\<) :: f:(a -> Tick b) -> t1:Tick a
    -> { t:Tick b | tval (f (tval t1))      == tval  t &&
         tcost t1 + tcost (f (tval t1)) - 2 == tcost t }
@-}
infixl 4 =\\<
(=\\<) :: (a -> Tick b) -> Tick a -> Tick b
f =\\< Tick m x = let Tick n y = f x in Tick (m + n - 2) y

-------------------------------------------------------------------------------
-- | Memoisation:
-------------------------------------------------------------------------------

{-@ reflect pay @-}
{-@ pay :: m:Int
    -> { t1:Tick a | m <= tcost t1 }
    -> { t:Tick ({ t2 : Tick a | tcost t1 - m == tcost t2 }) | m == tcost t }
@-}
pay :: Int -> Tick a -> Tick (Tick a)
pay m (Tick n x) = Tick m (Tick (n - m) x)


{-@ reflect zipWithM @-}
{-@ zipWithM :: f:(a -> b -> Tick c) -> x:Tick a -> y:Tick b
-> {t:Tick c | tcost t == tcost x + tcost y + tcost (f (tval x) (tval y))} @-}
zipWithM :: (a -> b -> Tick c) -> Tick a -> Tick b -> Tick c
zipWithM f (Tick c1 x1) (Tick c2 x2) = let Tick c x = f x1 x2 in Tick (c + c1 + c2) x
