{-# LANGUAGE TupleSections             #-}

module Language.Haskell.Liquid.Misc where

import Prelude hiding (error)
import Control.Monad.State

import Control.Arrow (first)
import System.FilePath

import           Control.Exception     (catch, IOException)
import qualified Data.HashSet          as S
import qualified Data.HashMap.Strict   as M
import qualified Data.List             as L
import           Data.Maybe
import           Data.Tuple
import           Data.Hashable
import           Data.Time
import           Data.Function (on)
import qualified Data.ByteString       as B
import           Data.ByteString.Char8 (pack, unpack)
import           Text.PrettyPrint.HughesPJ ((<>), char, Doc)
import           Text.Printf
import           Language.Fixpoint.Misc
import           Paths_liquidhaskell

type Nat = Int

timedAction :: (Show msg) => Maybe msg -> IO a -> IO a
timedAction label io = do
  t0 <- getCurrentTime
  a <- io
  t1 <- getCurrentTime
  let time = realToFrac (t1 `diffUTCTime` t0) :: Double
  case label of
    Just x  -> printf "Time (%.2fs) for action %s \n" time (show x)
    Nothing -> return ()
  return a

(!?) :: [a] -> Int -> Maybe a
[]     !? _ = Nothing
(x:_)  !? 0 = Just x
(_:xs) !? n = xs !? (n-1)

safeFromJust :: String -> Maybe t -> t
safeFromJust _  (Just x) = x
safeFromJust err _       = errorstar err

fst4 :: (t, t1, t2, t3) -> t
fst4 (a,_,_,_) = a

snd4 :: (t, t1, t2, t3) -> t1
snd4 (_,b,_,_) = b

mapFourth4 :: (t -> t4) -> (t1, t2, t3, t) -> (t1, t2, t3, t4)
mapFourth4 f (x, y, z, w) = (x, y, z, f w)

addFst3 :: t -> (t1, t2) -> (t, t1, t2)
addFst3   a (b, c) = (a, b, c)

addThd3 :: t2 -> (t, t1) -> (t, t1, t2)
addThd3   c (a, b) = (a, b, c)

dropFst3 :: (t, t1, t2) -> (t1, t2)
dropFst3 (_, x, y) = (x, y)

dropThd3 :: (t1, t2, t) -> (t1, t2)
dropThd3 (x, y, _) = (x, y)

replaceN :: (Enum a, Eq a, Num a) => a -> t -> [t] -> [t]
replaceN n y ls = [if i == n then y else x | (x, i) <- zip ls [0..]]

fourth4 :: (t, t1, t2, t3) -> t3
fourth4 (_,_,_,x) = x

third4 :: (t, t1, t2, t3) -> t2
third4  (_,_,x,_) = x

mapSndM :: (Applicative m) => (b -> m c) -> (a, b) -> m (a, c)
-- mapSndM f (x, y) = return . (x,) =<< f y
mapSndM f (x, y) = (x, ) <$> f y

firstM :: Functor f => (t -> f a) -> (t, t1) -> f (a, t1)
firstM  f (a,b) = (,b) <$> f a

secondM :: Functor f => (t -> f a) -> (t1, t) -> f (t1, a)
secondM f (a,b) = (a,) <$> f b

first3M :: Functor f => (t -> f a) -> (t, t1, t2) -> f (a, t1, t2)
first3M  f (a,b,c) = (,b,c) <$> f a

second3M :: Functor f => (t -> f a) -> (t1, t, t2) -> f (t1, a, t2)
second3M f (a,b,c) = (a,,c) <$> f b

third3M :: Functor f => (t -> f a) -> (t1, t2, t) -> f (t1, t2, a)
third3M  f (a,b,c) = (a,b,) <$> f c

third3 :: (t -> t3) -> (t1, t2, t) -> (t1, t2, t3)
third3 f (a,b,c) = (a,b,f c)

zip4 :: [t] -> [t1] -> [t2] -> [t3] -> [(t, t1, t2, t3)]
zip4 (x1:xs1) (x2:xs2) (x3:xs3) (x4:xs4) = (x1, x2, x3, x4) : zip4 xs1 xs2 xs3 xs4
zip4 _ _ _ _                             = []


getIncludeDir :: IO FilePath
getIncludeDir      = dropFileName <$> getDataFileName ("include" </> "Prelude.spec")

getCssPath :: IO FilePath
getCssPath         = getDataFileName $ "syntax" </> "liquid.css"

getCoreToLogicPath :: IO FilePath
getCoreToLogicPath = fmap (</> "CoreToLogic.lg") getIncludeDir


{-@ type ListN a N = {v:[a] | len v = N} @-}
{-@ type ListL a L = ListN a (len L) @-}

{-@ safeZipWithError :: _ -> xs:[a] -> ListL b xs -> ListL (a,b) xs / [xs] @-}
safeZipWithError :: String -> [t] -> [t1] -> [(t, t1)]
safeZipWithError msg (x:xs) (y:ys) = (x,y) : safeZipWithError msg xs ys
safeZipWithError _   []     []     = []
safeZipWithError msg _      _      = errorstar msg

safeZip3WithError :: String -> [t] -> [t1] -> [t2] -> [(t, t1, t2)]
safeZip3WithError msg (x:xs) (y:ys) (z:zs) = (x,y,z) : safeZip3WithError msg xs ys zs
safeZip3WithError _   []     []     []     = []
safeZip3WithError msg _      _      _      = errorstar msg

mapNs :: (Eq a, Num a, Foldable t) => t a -> (a1 -> a1) -> [a1] -> [a1]
mapNs ns f xs = foldl (\xs n -> mapN n f xs) xs ns

mapN :: (Eq a, Num a) => a -> (a1 -> a1) -> [a1] -> [a1]
mapN 0 f (x:xs) = f x : xs
mapN n f (x:xs) = x : mapN (n-1) f xs
mapN _ _ []     = []

zipWithDefM :: Monad m => (a -> a -> m a) -> [a] -> [a] -> m [a]
zipWithDefM _ []     []     = return []
zipWithDefM _ xs     []     = return xs
zipWithDefM _ []     ys     = return ys
zipWithDefM f (x:xs) (y:ys) = liftM2 (:) (f x y) (zipWithDefM f xs ys)

--------------------------------------------------------------------------------
-- Originally part of Fixpoint's Misc:
--------------------------------------------------------------------------------

single :: t -> [t]
single x = [x]

mapFst3 :: (t -> t1) -> (t, t2, t3) -> (t1, t2, t3)
mapFst3 f (x, y, z) = (f x, y, z)

mapSnd3 :: (t -> t2) -> (t1, t, t3) -> (t1, t2, t3)
mapSnd3 f (x, y, z) = (x, f y, z)

mapThd3 :: (t -> t3) -> (t1, t2, t) -> (t1, t2, t3)
mapThd3 f (x, y, z) = (x, y, f z)


hashMapMapWithKey   :: (k -> v1 -> v2) -> M.HashMap k v1 -> M.HashMap k v2
hashMapMapWithKey f = fromJust . M.traverseWithKey (\k v -> Just (f k v))

hashMapMapKeys      :: (Eq k, Hashable k) => (t -> k) -> M.HashMap t v -> M.HashMap k v
hashMapMapKeys f    = M.fromList . fmap (first f) . M.toList

concatMapM :: (Monad f, Traversable t) => (a1 -> f [a]) -> t a1 -> f [a]
concatMapM f = fmap concat . mapM f

firstElems ::  [(B.ByteString, B.ByteString)] -> B.ByteString -> Maybe (Int, B.ByteString, (B.ByteString, B.ByteString))
firstElems seps str
  = case splitters seps str of
      [] -> Nothing
      is -> Just $ L.minimumBy (compare `on` fst3) is

splitters :: [(B.ByteString, t)]
          -> B.ByteString -> [(Int, t, (B.ByteString, B.ByteString))]
splitters seps str
  = [(i, c', z) | (c, c') <- seps
                , let z   = B.breakSubstring c str
                , let i   = B.length (fst z)
                , i < B.length str                 ]

bchopAlts :: [(B.ByteString, B.ByteString)] -> B.ByteString -> [B.ByteString]
bchopAlts seps  = go
  where
    go  s               = maybe [s] go' (firstElems seps s)
    go' (_,c',(s0, s1)) = if B.length s2 == B.length s1 then [B.concat [s0,s1]] else s0 : s2' : go s3'
                          where (s2, s3) = B.breakSubstring c' s1
                                s2'      = B.append s2 c'
                                s3'      = B.drop (B.length c') s3

chopAlts :: [(String, String)] -> String -> [String]
chopAlts seps str = unpack <$> bchopAlts [(pack c, pack c') | (c, c') <- seps] (pack str)

sortDiff :: (Ord a) => [a] -> [a] -> [a]
sortDiff x1s x2s             = go (sortNub x1s) (sortNub x2s)
  where
    go xs@(x:xs') ys@(y:ys')
      | x <  y               = x : go xs' ys
      | x == y               = go xs' ys'
      | otherwise            = go xs ys'
    go xs []                 = xs
    go [] _                  = []

angleBrackets :: Doc -> Doc
angleBrackets p    = char '<' <> p <> char '>'

mkGraph :: (Eq a, Eq b, Hashable a, Hashable b) => [(a, b)] -> M.HashMap a (S.HashSet b)
mkGraph = fmap S.fromList . group

tryIgnore :: String -> IO () -> IO ()
tryIgnore s a = catch a $ \e ->
                do let err = show (e :: IOException)
                   writeLoud ("Warning: Couldn't do " ++ s ++ ": " ++ err)
                   return ()

(=>>) :: Monad m => m b -> (b -> m a) -> m b
(=>>) m f = m >>= (\x -> f x >> return x)

(<<=) :: Monad m => (b -> m a) -> m b -> m b
(<<=) = flip (=>>)



firstJust :: (a -> Maybe b) -> [a] -> Maybe b
firstJust f xs = listToMaybe $ mapMaybe f xs

intToString :: Int -> String
intToString 1 = "1st"
intToString 2 = "2nd"
intToString 3 = "3rd"
intToString n = show n ++ "th"

mapAccumM :: (Monad m, Traversable t) => (a -> b -> m (a, c)) -> a -> t b -> m (a, t c)
mapAccumM f acc0 xs =
  swap <$> runStateT (traverse (StateT . (\x acc -> swap <$> f acc x)) xs) acc0
