{-# LANGUAGE ScopedTypeVariables #-}

module Language.Haskell.Liquid.Misc where

import Text.Printf (printf)
import Control.Monad.State
import qualified Control.Exception as Ex
import System.Directory

import System.Environment

import qualified Data.Set as S 
import qualified Data.Map as M
import Data.List 
import Debug.Trace (trace)
import Data.Maybe
import Control.DeepSeq

---------------------------------------------------------------------
-- ($!!) f x = x `deepseq` f x

--instance (NFData a, NFData b) => NFData (M.Map a b) where
--  rnf _ = ()
--
--instance (NFData a) => NFData (S.Set a) where
--  rnf _ = ()
--

---------------------------------------------------------------------

unIntersperse x ys
  = case elemIndex x ys of
      Nothing -> [ys]
      Just i  -> let (y, _:ys') = splitAt i ys 
                 in (y : unIntersperse x ys')

(=>>) m f = m >>= (\x -> f x >> return x)

wrap l r s = l ++ s ++ r

repeats n  = concat . replicate n

errorstar = error . wrap (stars ++ "\n") (stars ++ "\n") 
  where stars = repeats 3 "\n**************************ERROR***************************************"

fst3 ::  (a, b, c) -> a
fst3 (x,_,_) = x

snd3 ::  (a, b, c) -> b
snd3 (_,x,_) = x

thd3 ::  (a, b, c) -> c
thd3 (_,_,x) = x


single ::  a -> [a]
single x = [x]

mapFst ::  (a1 -> a2) -> (a1, b) -> (a2, b)
mapFst f (x, y)  = (f x, y)

mapSnd ::  (b1 -> b2) -> (a, b1) -> (a, b2)
mapSnd f (x, y)  = (x, f y)

mapPair ::  (a -> b) -> (a, a) -> (b, b)
mapPair f (x, y) = (f x, f y)

mlookup ::  (Show k, Ord k) => M.Map k v -> k -> v
mlookup m k 
  = case M.lookup k m of
      Just v  -> v
      Nothing -> errorstar $ "mlookup: unknown key " ++ show k


mfromJust ::  String -> Maybe a -> a
mfromJust _ (Just x) = x 
mfromJust s Nothing  = errorstar $ "mfromJust: Nothing " ++ s

boxStrCat ::  String -> [String] -> String 
boxStrCat sep = ("[" ++) . (++ "]") . intercalate sep 

tryIgnore :: String -> IO () -> IO ()
tryIgnore s a = Ex.catch a $ \e -> 
                do let err = show (e :: Ex.IOException)
                   putStrLn ("Warning: Couldn't do " ++ s ++ ": " ++ err)
                   return ()

traceShow ::  Show a => String -> a -> a
traceShow s x = trace ("\nTrace: " ++ s ++ " : " ++ show x) $ x

groupMap ::  Ord k => (a -> k) -> [a] -> M.Map k [a]
groupMap f xs = foldl' adds M.empty $ zip (map f xs) xs
  where adds  m (k, x) = M.insert k (x:finds m k) m  
        finds m k      = case M.lookup k m of
                           Just xs -> xs
                           Nothing -> []

nubSort :: (Ord a) => [a] -> [a]
nubSort = nubOrd . sort
  where nubOrd (x:t@(y:zs)) 
          | x == y    = nubOrd t 
          | otherwise = x : nubOrd t
        nubOrd xs = xs

distinct ::  Ord a => [a] -> Bool
distinct xs = length xs == length (nubSort xs)

tr_reverse ::  [a] -> [a]
tr_reverse      = foldl' (flip (:)) []  

tr_foldr' ::  (a -> b -> b) -> b -> [a] -> b
tr_foldr' f b   = foldl' (flip f) b . tr_reverse 

reduce f (x:xs) = foldl' f x xs
reduce f _      = errorstar $ "reduce called on empty list!"

safeZip msg xs ys 
  | length xs == length ys 
  = zip xs ys
  | otherwise              
  = errorstar $ "lzip called on non-eq-sized lists"


safeUnion msg m1 m2 = 
  case Data.List.find (`M.member` m1) (M.keys m2) of
    Just k  -> errorstar $ "safeUnion with common key = " ++ show k ++ " " ++ msg
    Nothing -> M.union m1 m2

safeHead msg (x:_) = x
safeHead msg _     = errorstar $ "safeHead with empty list " ++ msg

memoIndex :: (Ord b) => (a -> Maybe b) -> [a] -> [Maybe Int]
memoIndex f = snd . mapAccumL foo M.empty 
  where 
  foo memo z =
    case f z of 
      Nothing -> (memo, Nothing)
      Just k  -> case k `M.lookup` memo of 
                   Just i  -> (memo, Just i)
                   Nothing -> (M.insert k (M.size memo) memo, Just (M.size memo))

checkFail ::  [Char] -> (a -> Bool) -> a -> a
checkFail msg f x 
  | f x
  = x
  | otherwise
  = errorstar $ "Check-Failure: " ++ msg

chopAfter ::  (a -> Bool) -> [a] -> [a]
chopAfter f xs 
  = case findIndex f xs of
      Just n  -> take n xs
      Nothing -> xs

chopPrefix p xs 
  | p `isPrefixOf` xs
  = Just $ drop (length p) xs
  | otherwise 
  = Nothing

findFirst ::  Monad m => (t -> m [a]) -> [t] -> m (Maybe a)
findFirst f []     = return Nothing
findFirst f (x:xs) = do r <- f x
                        case r of 
                          y:_ -> return (Just y)
                          []  -> findFirst f xs

testM f x = do b <- f x
               return $ if b then [x] else [] 

--fixM :: (a -> m (Maybe a)) -> a -> m (Maybe a)
--fixM f x = do xo' <- f x
--              case xo' of
--                Just x' -> fixM f x'
--                Nothing -> return x
