-- monadic computations
-- (contributed by Vivian McPhail)

import Numeric.LinearAlgebra
import Control.Monad.State.Strict
import Control.Monad.Maybe
import Foreign.Storable(Storable)
import System.Random(randomIO)

-------------------------------------------

-- an instance of MonadIO, a monad transformer
type VectorMonadT = StateT Int IO

test1 :: Vector Int -> IO (Vector Int)
test1 = mapVectorM $ \x -> do
    putStr $ (show x) ++ " "
    return (x + 1)

-- we can have an arbitrary monad AND do IO
addInitialM :: Vector Int -> VectorMonadT ()
addInitialM = mapVectorM_ $ \x -> do
    i <- get
    liftIO $ putStr $ (show $ x + i) ++ " "
    put $ x + i

-- sum the values of the even indiced elements
sumEvens :: Vector Int -> Int
sumEvens = foldVectorWithIndex (\x a b -> if x `mod` 2 == 0 then a + b else b) 0

-- sum and print running total of evens
sumEvensAndPrint :: Vector Int -> VectorMonadT ()
sumEvensAndPrint = mapVectorWithIndexM_ $ \ i x -> do
    when (i `mod` 2 == 0) $ do
        v <- get
        put $ v + x
        v' <- get
        liftIO $ putStr $ (show v') ++ " "


indexPlusSum :: Vector Int -> VectorMonadT ()
indexPlusSum v' = do
    let f i x = do
            s <- get
            let inc = x+s
            liftIO $ putStr $ show (i,inc) ++ " "
            put inc
            return inc
    v <- mapVectorWithIndexM f v'
    liftIO $ do
        putStrLn ""
        putStrLn $ show v

-------------------------------------------

-- short circuit
monoStep :: Double -> MaybeT (State Double) ()
monoStep d = do
    dp <- get
    when (d < dp) (fail "negative difference")
    put d
{-# INLINE monoStep #-}

isMonotoneIncreasing :: Vector Double -> Bool
isMonotoneIncreasing v =
    let res = evalState (runMaybeT $ (mapVectorM_ monoStep v)) (v @> 0)
     in case res of
        Nothing -> False
        Just _  -> True


-------------------------------------------

-- | apply a test to successive elements of a vector, evaluates to true iff test passes for all pairs
successive_ :: Storable a => (a -> a -> Bool) -> Vector a -> Bool
successive_ t v = maybe False (\_ -> True) $ evalState (runMaybeT (mapVectorM_ step (subVector 1 (dim v - 1) v))) (v @> 0)
   where step e = do
                  ep <- lift $ get
                  if t e ep
                     then lift $ put e
                     else (fail "successive_ test failed")

-- | operate on successive elements of a vector and return the resulting vector, whose length 1 less than that of the input
successive :: (Storable a, Storable b) => (a -> a -> b) -> Vector a -> Vector b
successive f v = evalState (mapVectorM step (subVector 1 (dim v - 1) v)) (v @> 0)
   where step e = do
                  ep <- get
                  put e
                  return $ f ep e

-------------------------------------------

v :: Vector Int
v = 10 |> [0..]

w = fromList ([1..10]++[10,9..1]) :: Vector Double


main = do
    v' <- test1 v
    putStrLn ""
    putStrLn $ show v'
    evalStateT (addInitialM v) 0
    putStrLn ""
    putStrLn $ show (sumEvens v)
    evalStateT (sumEvensAndPrint v) 0
    putStrLn ""
    evalStateT (indexPlusSum v) 0
    putStrLn "-----------------------"
    mapVectorM_ print v
    print =<< (mapVectorM (const randomIO) v :: IO (Vector Double))
    print =<< (mapVectorM (\a -> fmap (+a) randomIO) (5|>[0,100..1000]) :: IO (Vector Double))
    putStrLn "-----------------------"
    print $ isMonotoneIncreasing w
    print $ isMonotoneIncreasing (subVector 0 7 w)
    print $ successive_ (>) v
    print $ successive_ (>) w
    print $ successive (+) v
