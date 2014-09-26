{-@ LIQUID "--no-termination" @-}
module Times where

import Foreign

{-@ times :: forall <p :: Int -> a -> Prop>. 
             n:Nat -> a<p 0> -> (m:{Nat | m <= n} -> a<p m> -> a<p (m+1)>) -> a<p n>
  @-}
times :: Int -> a -> (Int -> a -> a) -> a
times n z f = go 0 z
  where
    go m z | m == n    = z
           | otherwise = go (m+1) (f m z)

{-@ predicate Btwn Lo N Hi = Lo <= N && N < Hi @-}
{-@ predicate Uint8 N = Btwn 0 N 256 @-}


{-@ assume addUint8 :: x:{Int | Uint8 x} -> y:{Int | Uint8 y && Uint8 (x+y)}
                    -> {v:Int | Uint8 v && v = x + y}
  @-}
addUint8 :: Int -> Int -> Int
addUint8 = (+)

{-@ ten :: {v:Int | Uint8 v} @-}
ten = times 10 0 (\n x -> add1 x)

{-@ gt10 :: x:Int -> {v:Bool | Prop v <=> x >= 10} @-}
gt10 :: Int -> Bool
gt10 x = x >= 10

{-@ add1 :: x:{Int | Btwn 0 x 255} -> {v:Int | Uint8 v && v = x + 1} @-}
add1 x = addUint8 x 1

{-@ qualif TimesTwo(v:int, x:int): v = x * 2 @-}
{-@ qualif PlusTwo(v:int, x:int): v = x + 2 @-}

timesM :: Int -> (Int -> IO ()) -> IO ()
timesM n f = go 0
  where
    go m | m == n    = return ()
         | otherwise = f m >> go (m+1)

{-@ tenM :: Ptr <{\x -> x = 0}> Int -> IO () @-}
tenM :: Ptr Int -> IO ()
tenM p = timesM 10 $ \i -> do
           x <- peek p
           poke p $ x `addUint8` 1

{-@ data Ptr a <p :: a -> Prop> = GHC.Ptr.Ptr (x::GHC.Base.Addr#) @-}

{-@ poke :: forall <p :: a -> Prop>. (Storable a)
         => Ptr <p> a
         -> a<p>
         -> (IO ())
  @-}

{-@ peek :: forall <p :: a -> Prop>. (Storable a)
         => (Ptr <p> a)
         -> (IO (a<p>))
  @-}
