{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DoAndIfThenElse #-}

module Language.Haskell.Liquid.Misc where

import Prelude hiding (error)
import Control.Monad.State

import Control.Arrow (first)
import System.FilePath
import System.Directory   (getModificationTime, doesFileExist)
import System.Environment (getExecutablePath)

import qualified Control.Exception     as Ex --(evaluate, catch, IOException)
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
import qualified Text.PrettyPrint.HughesPJ as PJ -- (char, Doc)
import           Text.Printf
import           Language.Fixpoint.Misc
import           Paths_liquidhaskell_boot

type Nat = Int

(.&&.), (.||.) :: (a -> Bool) -> (a -> Bool) -> a -> Bool
(.&&.) = up (&&)
(.||.) = up (||)

up :: (b -> c -> d) -> (a -> b) -> (a -> c) -> (a -> d)
up o f g x = f x `o` g x

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

safeFromLeft :: String -> Either a b -> a
safeFromLeft _   (Left l) = l
safeFromLeft err _        = errorstar err


takeLast :: Int -> [a] -> [a]
takeLast n xs = drop (m - n) xs
  where
    m         = length xs

getNth :: Int -> [a] -> Maybe a
getNth 0 (x:_)  = Just x
getNth n (_:xs) = getNth (n-1) xs
getNth _ _      = Nothing

fst4 :: (t, t1, t2, t3) -> t
fst4 (a,_,_,_) = a

snd4 :: (t, t1, t2, t3) -> t1
snd4 (_,b,_,_) = b

thd4 :: (t1, t2, t3, t4) -> t3
thd4 (_,_,b,_) = b


thrd3 :: (t1, t2, t3) -> t3
thrd3 (_,_,c) = c

mapFifth5 :: (t -> t4) -> (t0, t1, t2, t3, t) -> (t0, t1, t2, t3, t4)
mapFifth5 f (a, x, y, z, w) = (a, x, y, z, f w)

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


thd5 :: (t0, t1, t2, t3,t4) -> t2
thd5 (_,_,x,_,_) = x

snd5 :: (t0, t1, t2, t3,t4) -> t1
snd5 (_,x,_,_,_) = x

fst5 :: (t0, t1, t2, t3,t4) -> t0
fst5 (x,_,_,_,_) = x

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

zip5 :: [t] -> [t1] -> [t2] -> [t3] -> [t4] -> [(t, t1, t2, t3, t4)]
zip5 (x1:xs1) (x2:xs2) (x3:xs3) (x4:xs4) (x5:xs5) = (x1, x2, x3, x4,x5) : zip5 xs1 xs2 xs3 xs4 xs5
zip5 _ _ _ _ _                                    = []



unzip4 :: [(t, t1, t2, t3)] -> ([t],[t1],[t2],[t3])
unzip4 = go [] [] [] []
  where go a1 a2 a3 a4 ((x1,x2,x3,x4):xs) = go (x1:a1) (x2:a2) (x3:a3) (x4:a4) xs
        go a1 a2 a3 a4 [] = (reverse  a1, reverse a2, reverse a3, reverse a4)


getCssPath :: IO FilePath
getCssPath         = getDataFileName $ "syntax" </> "liquid.css"

getCoreToLogicPath :: IO FilePath
getCoreToLogicPath = do
    let fileName = "CoreToLogic.lg"

    -- Try to find it first at executable path
    exePath <- dropFileName <$> getExecutablePath
    let atExe = exePath </> fileName
    exists <- doesFileExist atExe

    if exists then
      return atExe
    else
      getDataFileName ("include" </> fileName)

{-@ type ListN a N = {v:[a] | len v = N} @-}
{-@ type ListL a L = ListN a (len L) @-}

zipMaybe :: [a] -> [b] -> Maybe [(a, b)]
zipMaybe xs ys
  | length xs == length ys = Just (zip xs ys)
  | otherwise              = Nothing

{-@ safeZipWithError :: _ -> xs:[a] -> ListL b xs -> ListL (a,b) xs / [xs] @-}
safeZipWithError :: String -> [t] -> [t1] -> [(t, t1)]
safeZipWithError msg (x:xs) (y:ys) = (x,y) : safeZipWithError msg xs ys
safeZipWithError _   []     []     = []
safeZipWithError msg _      _      = errorstar msg

safeZip3WithError :: String -> [t] -> [t1] -> [t2] -> [(t, t1, t2)]
safeZip3WithError msg (x:xs) (y:ys) (z:zs) = (x,y,z) : safeZip3WithError msg xs ys zs
safeZip3WithError _   []     []     []     = []
safeZip3WithError msg _      _      _      = errorstar msg

safeZip4WithError :: String -> [t1] -> [t2] -> [t3] -> [t4] -> [(t1, t2, t3, t4)]
safeZip4WithError msg (x:xs) (y:ys) (z:zs) (w:ws) = (x,y,z,w) : safeZip4WithError msg xs ys zs ws
safeZip4WithError _   []     []     []     []     = []
safeZip4WithError msg _      _      _      _      = errorstar msg


mapNs :: (Eq a, Num a, Foldable t) => t a -> (a1 -> a1) -> [a1] -> [a1]
mapNs ns f xs = foldl (\ys n -> mapN n f ys) xs ns

mapN :: (Eq a, Num a) => a -> (a1 -> a1) -> [a1] -> [a1]
mapN 0 f (x:xs) = f x : xs
mapN n f (x:xs) = x : mapN (n-1) f xs
mapN _ _ []     = []

zipWithDefM :: Monad m => (a -> a -> m a) -> [a] -> [a] -> m [a]
zipWithDefM _ []     []     = return []
zipWithDefM _ xs     []     = return xs
zipWithDefM _ []     ys     = return ys
zipWithDefM f (x:xs) (y:ys) = (:) <$> f x y <*> zipWithDefM f xs ys

zipWithDef :: (a -> a -> a) -> [a] -> [a] -> [a]
zipWithDef _ []     []     = []
zipWithDef _ xs     []     = xs
zipWithDef _ []     ys     = ys
zipWithDef f (x:xs) (y:ys) = f x y : zipWithDef f xs ys


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

firstMaybes :: [Maybe a] -> Maybe a
firstMaybes = listToMaybe . catMaybes

fromFirstMaybes :: a -> [Maybe a] -> a
fromFirstMaybes x = fromMaybe x . firstMaybes
-- fromFirstMaybes x = fromMaybe x . listToMaybe . catMaybes

hashMapMapWithKey   :: (k -> v1 -> v2) -> M.HashMap k v1 -> M.HashMap k v2
hashMapMapWithKey f = fromJust . M.traverseWithKey (\k v -> Just (f k v))

hashMapMapKeys   :: (Eq k2, Hashable k2) => (k1 -> k2) -> M.HashMap k1 v -> M.HashMap k2 v
hashMapMapKeys f = M.fromList . fmap (first f) . M.toList

concatMapM :: (Monad m, Traversable t) => (a -> m [b]) -> t a -> m [b]
concatMapM f = fmap concat . mapM f

replaceSubset :: (Eq k, Hashable k) => [(k, a)] -> [(k, a)] -> [(k, a)]
replaceSubset kvs kvs' = M.toList (L.foldl' upd m0 kvs')
  where
    m0                = M.fromList kvs
    upd m (k, v')
      | M.member k m  = M.insert k v' m
      | otherwise     = m

replaceWith :: (Eq a, Hashable a) => (b -> a) -> [b] -> [b] -> [b]
replaceWith f xs ys = snd <$> replaceSubset xs' ys'
  where
    xs'             = [ (f x, x) | x <- xs ]
    ys'             = [ (f y, y) | y <- ys ]




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

(<->) :: PJ.Doc -> PJ.Doc -> PJ.Doc
x <-> y = x PJ.<> y

angleBrackets :: PJ.Doc -> PJ.Doc
angleBrackets p = PJ.char '<' <-> p <-> PJ.char '>'

mkGraph :: (Eq a, Eq b, Hashable a, Hashable b) => [(a, b)] -> M.HashMap a (S.HashSet b)
mkGraph = fmap S.fromList . group

tryIgnore :: String -> IO () -> IO ()
tryIgnore s a =
  Ex.catch a $ \e -> do
    let err = show (e :: Ex.IOException)
    writeLoud ("Warning: Couldn't do " ++ s ++ ": " ++ err)
    return ()


condNull :: Monoid m => Bool -> m -> m
condNull c xs = if c then xs else mempty

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

ifM :: (Monad m) => m Bool -> m b -> m b -> m b
ifM b x y = b >>= \z -> if z then x else y

nubHashOn :: (Eq k, Hashable k) => (a -> k) -> [a] -> [a]
nubHashOn f = map head . M.elems . groupMap f

nubHashLast :: (Eq k, Hashable k) => (a -> k) -> [a] -> [a]
nubHashLast f xs = M.elems $ M.fromList [ (f x, x) | x <- xs ]

nubHashLastM :: (Eq k, Hashable k, Monad m) => (a -> m k) -> [a] -> m [a]
nubHashLastM f xs =  M.elems . M.fromList . (`zip` xs) <$> mapM f xs

uniqueByKey :: (Eq k, Hashable k) => [(k, v)] -> Either (k, [v]) [v]
uniqueByKey = uniqueByKey' tx
  where
    tx (_, [v]) = Right v
    tx (k, vs)  = Left  (k, vs)

uniqueByKey' :: (Eq k, Hashable k) => ((k, [v]) -> Either e v) -> [(k, v)] -> Either e [v]
uniqueByKey' tx = mapM tx . groupList


join :: (Eq b, Hashable b) => [(a, b)] -> [(b, c)] -> [(a, c)]
join aBs bCs = [ (a, c) | (a, b) <- aBs, c <- b2cs b ]
  where
    bM       = M.fromList bCs
    b2cs b   = maybeToList (M.lookup b bM)


fstByRank :: (Ord r, Hashable k, Eq k) => [(r, k, v)] -> [(r, k, v)]
fstByRank rkvs = [ (r, k, v) | (k, rvs) <- krvss, let (r, v) = getFst rvs ]
  where
    getFst     = head . sortOn fst
    krvss      = groupList [ (k, (r, v)) | (r, k, v) <- rkvs ]

sortOn :: (Ord b) => (a -> b) -> [a] -> [a]
sortOn f = L.sortBy (compare `on` f)

firstGroup :: (Eq k, Ord k, Hashable k) => [(k, a)] -> [a]
firstGroup kvs = case groupList kvs of
  []   -> []
  kvss -> snd . head . sortOn fst $ kvss

{- mapEither :: (a -> Either b c) -> [a] -> ([b], [c])
mapEither f []     = ([], [])
mapEither f (x:xs) = case f x of 
                       Left y  -> (y:ys, zs)
                       Right z -> (ys, z:zs)
                     where 
                       (ys, zs) = mapEither f xs 
-}
mapErr :: (a -> Either e b) -> [a] -> Either [e] [b]
mapErr f xs = catEithers (map f xs)

catEithers :: [ Either a b ] -> Either [a] [b]
catEithers zs = case ls of
  [] -> Right rs
  _  -> Left ls
  where
    ls = [ l | Left  l <- zs ]
    rs = [ r | Right r <- zs ]


keyDiff :: (Eq k, Hashable k) => (a -> k) -> [a] -> [a] -> [a]
keyDiff f x1s x2s = M.elems (M.difference (m x1s) (m x2s))
  where
    m xs          = M.fromList [(f x, x) | x <- xs]

concatUnzip :: [([a], [b])] -> ([a], [b])
concatUnzip xsyss = (concatMap fst xsyss, concatMap snd xsyss)


sayReadFile :: FilePath -> IO String
sayReadFile f = do
  -- print ("SAY-READ-FILE: " ++ f)
  res <- readFile f
  Ex.evaluate res

lastModified :: FilePath -> IO (Maybe UTCTime)
lastModified f = do
  ex  <- doesFileExist f
  if ex then Just <$> getModificationTime f
        else return   Nothing


data Validate e a = Err e | Val a

instance Functor (Validate e) where
  fmap _ (Err e) = Err e
  fmap f (Val v)  = Val (f v)

instance Monoid e => Applicative (Validate e) where
  pure = Val
  (Err e1) <*> Err e2 = Err (e1 <> e2)
  (Err e1) <*> _      = Err e1
  _        <*> Err e2 = Err e2
  (Val f)  <*> Val x  = Val (f x)
