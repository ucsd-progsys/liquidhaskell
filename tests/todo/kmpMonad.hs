{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--diff"           @-}

module KMP (search) where

import Language.Haskell.Liquid.Prelude (liquidError, liquidAssert)
import Data.IORef
import Control.Applicative ((<$>))
import qualified Data.Map as M
import Prelude hiding (map)

{-@ type Upto N = {v:Nat | v < N} @-}

---------------------------------------------------------------------------
{-@ search :: pat:String -> str:String -> IO (Maybe (Upto (len str))) @-}
---------------------------------------------------------------------------
search :: String -> String -> IO (Maybe Int)
search pat str = do
  p <- ofListIO pat
  s <- ofListIO str
  kmpSearch p s

---------------------------------------------------------------------------
-- | Do the Search --------------------------------------------------------
---------------------------------------------------------------------------

kmpSearch p@(IOA m _) s@(IOA n _) = do
  t <- kmpTable p
  find p s t 0 0

find p@(IOA m _) s@(IOA n _) t = go
  where
    go i j
      | i >= n    = return $ Nothing
      | j >= m    = return $ Just (i - m)
      | otherwise = do si <- getIO s i
                       pj <- getIO p j
                       tj <- getIO t j
                       case () of
                        _ | si == pj  -> go (i+1) (j+1)
                          | j == 0    -> go (i+1) j
                          | otherwise -> go i     tj

---------------------------------------------------------------------------
-- | Make Table -----------------------------------------------------------
---------------------------------------------------------------------------

-- BUG WHAT's going on? 
{-@ bob :: Nat -> IO () @-}
bob n = do
  t <- newIO (n + 1) (\_ -> 0)
  setIO t 0 100
  r <- getIO t 0
  liquidAssert (r == 100) $ return ()


kmpTable p@(IOA m _) = do
  t <- newIO m (\_ -> 0)
  fill p t 1 0
  return t

fill p t@(IOA m _) = go
  where
    go i j
      | i < m - 1  = do
          pi <- getIO p (id i)
          pj <- getIO p j
          case () of
            _ | pi == pj -> do
                  let i' = i + 1
                  let j' = j + 1
                  setIO t i' j'
                  go i' j'
              | j == 0 -> do
                  let i' = i + 1
                  setIO t i' 0
                  go i' j
              | otherwise -> do
                  j' <- getIO t j
                  go i j'
      | otherwise = return t


-------------------------------------------------------------------------------
-- | An Imperative Array ------------------------------------------------------
-------------------------------------------------------------------------------

data IOArr a = IOA { size :: Int
                   , pntr :: IORef (Arr a)
                   }

{-@ data IOArr a <p :: Int -> a -> Prop>
      = IOA { size :: Nat
            , pntr :: IORef ({v:Arr<p> a | alen v = size})
            }
  @-}


{-@ newIO :: forall <p :: Int -> a -> Prop>.
               n:Nat -> (i:Upto n -> a<p i>) -> IO ({v: IOArr<p> a | size v = n})
  @-}
newIO n f = IOA n <$> newIORef (new n f)

{-@ getIO :: forall <p :: Int -> a -> Prop>.
              a:IOArr<p> a -> i:Upto (size a) -> IO (a<p i>)
  @-}
getIO a@(IOA sz p) i
  = do arr   <- readIORef p
       return $ (arr ! i)

{-@ setIO :: forall <p :: Int -> a -> Prop>.
              a:IOArr<p> a -> i:Upto (size a) -> a<p i> -> IO ()
  @-}
setIO a@(IOA sz p) i v
  = do arr     <- readIORef p
       let arr' = set arr i v
       writeIORef p arr'


{-@ ofListIO :: xs:[a] -> IO ({v:IOArr a | size v = len xs}) @-}
ofListIO xs  = newIO n f
  where
    n        = length xs
    m        = M.fromList $ zip [0..] xs
    f i      = (M.!) m i


{-@ mapIO :: (a -> b) -> a:IOArr a -> IO ({v:IOArr b | size v = size a}) @-}
mapIO f (IOA n p)
  = do a <- readIORef p
       IOA n <$> newIORef (map f a)



-------------------------------------------------------------------------------
-- | A Pure Array -------------------------------------------------------------
-------------------------------------------------------------------------------

data Arr a   = A { alen :: Int
                 , aval :: Int -> a
                 }

{-@ data Arr a <p :: Int -> a -> Prop>
             = A { alen :: Nat
                 , aval :: i:Upto alen -> a<p i>
                 }
  @-}


{-@ new :: forall <p :: Int -> a -> Prop>.
             n:Nat -> (i:Upto n -> a<p i>) -> {v: Arr<p> a | alen v = n}
  @-}
new n v = A { alen = n
            , aval = \i -> if (0 <= i && i < n)
                             then v i
                             else liquidError "Out of Bounds!"
            }

{-@ (!) :: forall <p :: Int -> a -> Prop>.
             a:Arr<p> a -> i:Upto (alen a) -> a<p i>
  @-}

(A _ f) ! i = f i

{-@ set :: forall <p :: Int -> a -> Prop>.
             a:Arr<p> a -> i:Upto (alen a) -> a<p i> -> {v:Arr<p> a | alen v = alen a}
  @-}
set a@(A _ f) i v = a { aval = \j -> if (i == j) then v else f j }


{-@ ofList :: xs:[a] -> {v:Arr a | alen v = len xs} @-}
ofList xs = new n f
  where
    n     = length xs
    m     = M.fromList $ zip [0..] xs
    f i   = (M.!) m i

{-@ map :: (a -> b) -> a:Arr a -> {v:Arr b | alen v = alen a} @-}
map f a@(A n z) = A n (f . z)
