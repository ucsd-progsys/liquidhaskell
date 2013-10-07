{-# LANGUAGE CPP #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Packed.Internal.Common
-- Copyright   :  (c) Alberto Ruiz 2007
-- License     :  GPL-style
--
-- Maintainer  :  Alberto Ruiz <aruiz@um.es>
-- Stability   :  provisional
-- Portability :  portable (uses FFI)
--
-- Development utilities.
--
-----------------------------------------------------------------------------
-- #hide

module Data.Packed.Internal.Common(
  Adapt,
  app1, app2, app3, app4,
  app5, app6, app7, app8, app9, app10,
  (//), check, mbCatch,
  splitEvery, common, compatdim,
  fi,
  table
) where

import Foreign
import Control.Monad(when)
import Foreign.C.String(peekCString)
import Foreign.C.Types
import Foreign.Storable.Complex()
import Data.List(transpose,intersperse)
import Control.Exception as E

{-@ safeTake :: n:Nat -> {v:[a] | (len v) >= n} -> {v:[a] | (len v) = n})@-}
safeTake 0 _      = []
safeTake n (x:xs) = x : safeTake (n-1) xs

{-@ safeTake :: n:Nat -> xs:{v:[a] | (len v) >= n} -> {v:[a] | (len v) = (len xs) - n} @-}
safeDrop 0 xs     = xs
safeDrop n (_:xs) = safeDrop (n-1) xs

{-@ splitEvery :: n:Nat -> {v:[a] | (length v) mod n = 0} -> [{v:[a] | (len v) = n}] @-}
-- | @splitEvery 3 [1..9] == [[1,2,3],[4,5,6],[7,8,9]]@
splitEvery :: Int -> [a] -> [[a]]
splitEvery _ [] = []
splitEvery k l  = safeTake k l : splitEvery k (safeDrop k l)

-- | obtains the common value of a property of a list
common :: (Eq a) => (b->a) -> [b] -> Maybe a
common f = commonval . map f where
    commonval :: (Eq a) => [a] -> Maybe a
    commonval [] = Nothing
    commonval [a] = Just a
    commonval (a:b:xs) = if a==b then commonval (b:xs) else Nothing

{-@ predicate Max V X Y =  V = if (X >= Y) then X else Y @-}

{-@ measure maxInts :: [Int] -> Int 
    maxInts []     = {v | v = (0 - 1)} 
    maxInts (x:xs) = {v | (Max v x (maxInts xs))}
  @-}

{-@ goo :: xs:[{v:Int | v = (len xs)}] -> Int @-}
goo :: [Int] -> Int
goo xs = 0

prop0 = goo [1]
prop1 = goo [2]

{-@ compatdim :: dims:{v:[{v:Nat | (v = 1 || v = (maxInts dims))}] | v =-> Maybe {v:Nat | (maxInt dims)} @-}
-- | common value with \"adaptable\" 1
compatdim :: [Int] -> Maybe Int
compatdim [] = Nothing
compatdim [a] = Just a
compatdim (a:b:xs) = if a==b || a==1 || b==1 then compatdim (max a b:xs) else Nothing

-- | Formatting tool
table :: String -> [[String]] -> String
table sep as = unlines . map unwords' $ transpose mtp where 
    mt = transpose as
    longs = map (maximum . map length) mt
    mtp = zipWith (\a b -> map (pad a) b) longs mt
    pad n str = replicate (n - length str) ' ' ++ str
    unwords' = concat . intersperse sep

-- | postfix function application (@flip ($)@)
(//) :: x -> (x -> y) -> y
infixl 0 //
(//) = flip ($)

-- | specialized fromIntegral
fi :: Int -> CInt
fi = fromIntegral

-- hmm..
ww2 w1 o1 w2 o2 f = w1 o1 $ w2 o2 . f
ww3 w1 o1 w2 o2 w3 o3 f = w1 o1 $ ww2 w2 o2 w3 o3 . f
ww4 w1 o1 w2 o2 w3 o3 w4 o4 f = w1 o1 $ ww3 w2 o2 w3 o3 w4 o4 . f
ww5 w1 o1 w2 o2 w3 o3 w4 o4 w5 o5 f = w1 o1 $ ww4 w2 o2 w3 o3 w4 o4 w5 o5 . f
ww6 w1 o1 w2 o2 w3 o3 w4 o4 w5 o5 w6 o6 f = w1 o1 $ ww5 w2 o2 w3 o3 w4 o4 w5 o5 w6 o6 . f
ww7 w1 o1 w2 o2 w3 o3 w4 o4 w5 o5 w6 o6 w7 o7 f = w1 o1 $ ww6 w2 o2 w3 o3 w4 o4 w5 o5 w6 o6 w7 o7 . f
ww8 w1 o1 w2 o2 w3 o3 w4 o4 w5 o5 w6 o6 w7 o7 w8 o8 f = w1 o1 $ ww7 w2 o2 w3 o3 w4 o4 w5 o5 w6 o6 w7 o7 w8 o8 . f
ww9 w1 o1 w2 o2 w3 o3 w4 o4 w5 o5 w6 o6 w7 o7 w8 o8 w9 o9 f = w1 o1 $ ww8 w2 o2 w3 o3 w4 o4 w5 o5 w6 o6 w7 o7 w8 o8 w9 o9 . f
ww10 w1 o1 w2 o2 w3 o3 w4 o4 w5 o5 w6 o6 w7 o7 w8 o8 w9 o9 w10 o10 f = w1 o1 $ ww9 w2 o2 w3 o3 w4 o4 w5 o5 w6 o6 w7 o7 w8 o8 w9 o9 w10 o10 . f

type Adapt f t r = t -> ((f -> r) -> IO()) -> IO()

type Adapt1 f t1 = Adapt f t1 (IO CInt) -> t1 -> String -> IO()
type Adapt2 f t1 r1 t2 = Adapt f t1 r1 -> t1 -> Adapt1 r1 t2
type Adapt3 f t1 r1 t2 r2 t3 = Adapt f t1 r1 -> t1 -> Adapt2 r1 t2 r2 t3
type Adapt4 f t1 r1 t2 r2 t3 r3 t4 = Adapt f t1 r1 -> t1 -> Adapt3 r1 t2 r2 t3 r3 t4
type Adapt5 f t1 r1 t2 r2 t3 r3 t4 r4 t5 = Adapt f t1 r1 -> t1 -> Adapt4 r1 t2 r2 t3 r3 t4 r4 t5
type Adapt6 f t1 r1 t2 r2 t3 r3 t4 r4 t5 r5 t6 = Adapt f t1 r1 -> t1 -> Adapt5 r1 t2 r2 t3 r3 t4 r4 t5 r5 t6
type Adapt7 f t1 r1 t2 r2 t3 r3 t4 r4 t5 r5 t6 r6 t7 = Adapt f t1 r1 -> t1 -> Adapt6 r1 t2 r2 t3 r3 t4 r4 t5 r5 t6 r6 t7
type Adapt8 f t1 r1 t2 r2 t3 r3 t4 r4 t5 r5 t6 r6 t7 r7 t8 = Adapt f t1 r1 -> t1 -> Adapt7 r1 t2 r2 t3 r3 t4 r4 t5 r5 t6 r6 t7 r7 t8
type Adapt9 f t1 r1 t2 r2 t3 r3 t4 r4 t5 r5 t6 r6 t7 r7 t8 r8 t9 = Adapt f t1 r1 -> t1 -> Adapt8 r1 t2 r2 t3 r3 t4 r4 t5 r5 t6 r6 t7 r7 t8 r8 t9
type Adapt10 f t1 r1 t2 r2 t3 r3 t4 r4 t5 r5 t6 r6 t7 r7 t8 r8 t9 r9 t10 = Adapt f t1 r1 -> t1 -> Adapt9 r1 t2 r2 t3 r3 t4 r4 t5 r5 t6 r6 t7 r7 t8 r8 t9 r9 t10

app1 :: f -> Adapt1 f t1
app2 :: f -> Adapt2 f t1 r1 t2
app3 :: f -> Adapt3 f t1 r1 t2 r2 t3
app4 :: f -> Adapt4 f t1 r1 t2 r2 t3 r3 t4
app5 :: f -> Adapt5 f t1 r1 t2 r2 t3 r3 t4 r4 t5
app6 :: f -> Adapt6 f t1 r1 t2 r2 t3 r3 t4 r4 t5 r5 t6
app7 :: f -> Adapt7 f t1 r1 t2 r2 t3 r3 t4 r4 t5 r5 t6 r6 t7
app8 :: f -> Adapt8 f t1 r1 t2 r2 t3 r3 t4 r4 t5 r5 t6 r6 t7 r7 t8
app9 :: f -> Adapt9 f t1 r1 t2 r2 t3 r3 t4 r4 t5 r5 t6 r6 t7 r7 t8 r8 t9
app10 :: f -> Adapt10 f t1 r1 t2 r2 t3 r3 t4 r4 t5 r5 t6 r6 t7 r7 t8 r8 t9 r9 t10

app1 f w1 o1 s = w1 o1 $ \a1 -> f // a1 // check s
app2 f w1 o1 w2 o2 s = ww2 w1 o1 w2 o2 $ \a1 a2 -> f // a1 // a2 // check s
app3 f w1 o1 w2 o2 w3 o3 s = ww3 w1 o1 w2 o2 w3 o3 $
     \a1 a2 a3 -> f // a1 // a2 // a3 // check s
app4 f w1 o1 w2 o2 w3 o3 w4 o4 s = ww4 w1 o1 w2 o2 w3 o3 w4 o4 $
     \a1 a2 a3 a4 -> f // a1 // a2 // a3 // a4 // check s
app5 f w1 o1 w2 o2 w3 o3 w4 o4 w5 o5 s = ww5 w1 o1 w2 o2 w3 o3 w4 o4 w5 o5 $
     \a1 a2 a3 a4 a5 -> f // a1 // a2 // a3 // a4 // a5 // check s
app6 f w1 o1 w2 o2 w3 o3 w4 o4 w5 o5 w6 o6 s = ww6 w1 o1 w2 o2 w3 o3 w4 o4 w5 o5 w6 o6 $
     \a1 a2 a3 a4 a5 a6 -> f // a1 // a2 // a3 // a4 // a5 // a6 // check s
app7 f w1 o1 w2 o2 w3 o3 w4 o4 w5 o5 w6 o6 w7 o7 s = ww7 w1 o1 w2 o2 w3 o3 w4 o4 w5 o5 w6 o6 w7 o7 $
     \a1 a2 a3 a4 a5 a6 a7 -> f // a1 // a2 // a3 // a4 // a5 // a6 // a7 // check s
app8 f w1 o1 w2 o2 w3 o3 w4 o4 w5 o5 w6 o6 w7 o7 w8 o8 s = ww8 w1 o1 w2 o2 w3 o3 w4 o4 w5 o5 w6 o6 w7 o7 w8 o8 $
     \a1 a2 a3 a4 a5 a6 a7 a8 -> f // a1 // a2 // a3 // a4 // a5 // a6 // a7 // a8 // check s
app9 f w1 o1 w2 o2 w3 o3 w4 o4 w5 o5 w6 o6 w7 o7 w8 o8 w9 o9 s = ww9 w1 o1 w2 o2 w3 o3 w4 o4 w5 o5 w6 o6 w7 o7 w8 o8 w9 o9 $
     \a1 a2 a3 a4 a5 a6 a7 a8 a9 -> f // a1 // a2 // a3 // a4 // a5 // a6 // a7 // a8 // a9 // check s
app10 f w1 o1 w2 o2 w3 o3 w4 o4 w5 o5 w6 o6 w7 o7 w8 o8 w9 o9 w10 o10 s = ww10 w1 o1 w2 o2 w3 o3 w4 o4 w5 o5 w6 o6 w7 o7 w8 o8 w9 o9 w10 o10 $
     \a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 -> f // a1 // a2 // a3 // a4 // a5 // a6 // a7 // a8 // a9 // a10 // check s



-- GSL error codes are <= 1024
-- | error codes for the auxiliary functions required by the wrappers
errorCode :: CInt -> String
errorCode 2000 = "bad size"
errorCode 2001 = "bad function code"
errorCode 2002 = "memory problem"
errorCode 2003 = "bad file"
errorCode 2004 = "singular"
errorCode 2005 = "didn't converge"
errorCode 2006 = "the input matrix is not positive definite"
errorCode 2007 = "not yet supported in this OS"
errorCode n    = "code "++show n


-- | clear the fpu
foreign import ccall unsafe "asm_finit" finit :: IO ()

-- | check the error code
check :: String -> IO CInt -> IO ()
check msg f = do
#if FINIT
    finit
#endif
    err <- f
    when (err/=0) $ if err > 1024
                      then (error (msg++": "++errorCode err)) -- our errors
                      else do                                 -- GSL errors
                        ps <- gsl_strerror err
                        s <- peekCString ps
                        error (msg++": "++s)
    return ()

-- | description of GSL error codes
foreign import ccall unsafe "gsl_strerror" gsl_strerror :: CInt -> IO (Ptr CChar)

-- | Error capture and conversion to Maybe
mbCatch :: IO x -> IO (Maybe x)
mbCatch act = E.catch (Just `fmap` act) f
    where f :: SomeException -> IO (Maybe x)
          f _ = return Nothing
