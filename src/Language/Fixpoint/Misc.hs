{-# LANGUAGE CPP #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE ImplicitParams            #-} -- ignore hlint

module Language.Fixpoint.Misc where

-- import           System.IO.Unsafe            (unsafePerformIO)
import           Control.Exception                (bracket_)
import           Data.Hashable
-- import           Data.IORef
import           Control.Arrow                    (second)
import           Control.Monad                    (when, forM_, filterM)
import qualified Data.HashMap.Strict              as M
import qualified Data.List                        as L
import           Data.Tuple                       (swap)
import           Data.Maybe
import           Data.Array                       hiding (indices)
import           Data.Function                    (on)
import qualified Data.Graph                       as G
import qualified Data.Tree                        as T
import           Data.Unique
import           Debug.Trace                      (trace)
import           System.Console.ANSI
import           System.Console.CmdArgs.Verbosity (whenLoud)
import           System.Process                   (system)
import           System.Directory                 (createDirectoryIfMissing)
import           System.FilePath                  (takeDirectory)
import           Text.PrettyPrint.HughesPJ        hiding (first)
import           System.IO                        (stdout, hFlush )
import           System.Exit                      (ExitCode)
import           Control.Concurrent.Async


#ifdef MIN_VERSION_located_base
import Prelude hiding (error, undefined)
import GHC.Err.Located
import GHC.Stack
#endif

type (|->) a b = M.HashMap a b

firstMaybe :: (a -> Maybe b) -> [a] -> Maybe b
firstMaybe f = listToMaybe . mapMaybe f


asyncMapM :: (a -> IO b) -> [a] -> IO [b]
asyncMapM f xs = mapM (async . f) xs >>= mapM wait

traceShow     ::  Show a => String -> a -> a
traceShow s x = trace ("\nTrace: [" ++ s ++ "] : " ++ show x)  x

hashMapToAscList :: Ord a => M.HashMap a b -> [(a, b)]
hashMapToAscList = L.sortBy (compare `on` fst) . M.toList

---------------------------------------------------------------
-- | Unique Int -----------------------------------------------
---------------------------------------------------------------

getUniqueInt :: IO Int
getUniqueInt = do
  n1 <- hashUnique <$> newUnique
  n2 <- hashUnique <$> newUnique
  return (n1 * n2)

---------------------------------------------------------------
-- | Edit Distance --------------------------------------------
---------------------------------------------------------------

editDistance :: Eq a => [a] -> [a] -> Int
editDistance xs ys = table ! (m, n)
    where
    (m,n) = (length xs, length ys)
    x     = array (1,m) (zip [1..] xs)
    y     = array (1,n) (zip [1..] ys)

    table :: Array (Int,Int) Int
    table = array bnds [(ij, dist ij) | ij <- range bnds]
    bnds  = ((0,0),(m,n))

    dist (0,j) = j
    dist (i,0) = i
    dist (i,j) = minimum [table ! (i-1,j) + 1, table ! (i,j-1) + 1,
        if x ! i == y ! j then table ! (i-1,j-1) else 1 + table ! (i-1,j-1)]

-----------------------------------------------------------------------------------
------------ Support for Colored Logging ------------------------------------------
-----------------------------------------------------------------------------------

data Moods = Ok | Loud | Sad | Happy | Angry

moodColor :: Moods -> Color
moodColor Ok    = Black
moodColor Loud  = Blue
moodColor Sad   = Magenta
moodColor Happy = Green
moodColor Angry = Red

wrapStars :: String -> String
wrapStars msg = "\n**** " ++ msg ++ " " ++ replicate (74 - length msg) '*'

withColor :: Color -> IO () -> IO ()
-- withColor _ act = act
withColor c act
   = do setSGR [ SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid c]
        act
        setSGR [ Reset]

colorStrLn :: Moods -> String -> IO ()
colorStrLn c       = withColor (moodColor c) . putStrLn

colorPhaseLn :: Moods -> String -> String -> IO ()
colorPhaseLn c msg = colorStrLn c . wrapStars .  (msg ++)

startPhase :: Moods -> String -> IO ()
startPhase c msg   = colorPhaseLn c "START: " msg >> colorStrLn Ok " "

doneLine   :: Moods -> String -> IO ()
doneLine   c msg   = colorPhaseLn c "DONE:  " msg >> colorStrLn Ok " "

donePhase :: Moods -> String -> IO ()
donePhase c str
  = case lines str of
      (l:ls) -> doneLine c l >> forM_ ls (colorPhaseLn c "") >> hFlush stdout
      _      -> return ()

putBlankLn :: IO ()
putBlankLn = putStrLn "" >> hFlush stdout

--------------------------------------------------------------------------------
wrap :: [a] -> [a] -> [a] -> [a]
wrap l r s = l ++ s ++ r

repeats :: Int -> [a] -> [a]
repeats n  = concat . replicate n

#ifdef MIN_VERSION_located_base
errorstar :: (?callStack :: CallStack) => String -> a
#endif

errorstar  = error . wrap (stars ++ "\n") (stars ++ "\n")
  where
    stars = repeats 3 $ wrapStars "ERROR"

fst3 ::  (a, b, c) -> a
fst3 (x,_,_) = x

snd3 ::  (a, b, c) -> b
snd3 (_,x,_) = x

thd3 ::  (a, b, c) -> c
thd3 (_,_,x) = x

secondM :: Functor f => (b -> f c) -> (a, b) -> f (a, c)
secondM act (x, y) = (x,) <$> act y

#ifdef MIN_VERSION_located_base
mlookup    :: (?callStack :: CallStack, Eq k, Show k, Hashable k) => M.HashMap k v -> k -> v
safeLookup :: (?callStack :: CallStack, Eq k, Hashable k) => String -> k -> M.HashMap k v -> v
mfromJust  :: (?callStack :: CallStack) => String -> Maybe a -> a
#else
mlookup    :: (Eq k, Show k, Hashable k) => M.HashMap k v -> k -> v
safeLookup :: (Eq k, Hashable k) => String -> k -> M.HashMap k v -> v
mfromJust  :: String -> Maybe a -> a
#endif

mlookup m k = fromMaybe err $ M.lookup k m
  where
    err     = errorstar $ "mlookup: unknown key " ++ show k

safeLookup msg k m   = fromMaybe (errorstar msg) (M.lookup k m)
mfromJust _ (Just x) = x
mfromJust s Nothing  = errorstar $ "mfromJust: Nothing " ++ s

inserts ::  (Eq k, Hashable k) => k -> v -> M.HashMap k [v] -> M.HashMap k [v]
inserts k v m = M.insert k (v : M.lookupDefault [] k m) m

removes ::  (Eq k, Hashable k, Eq v) => k -> v -> M.HashMap k [v] -> M.HashMap k [v]
removes k v m = M.insert k (L.delete v (M.lookupDefault [] k m)) m

count :: (Eq k, Hashable k) => [k] -> [(k, Int)]
count = M.toList . fmap sum . group . fmap (, 1)

group :: (Eq k, Hashable k) => [(k, v)] -> M.HashMap k [v]
group = groupBase M.empty

groupBase :: (Eq k, Hashable k) => M.HashMap k [v] -> [(k, v)] -> M.HashMap k [v]
groupBase = L.foldl' (\m (k, v) -> inserts k v m)

groupList :: (Eq k, Hashable k) => [(k, v)] -> [(k, [v])]
groupList = M.toList . group

groupMap   :: (Eq k, Hashable k) => (a -> k) -> [a] -> M.HashMap k [a]
groupMap f = L.foldl' (\m x -> inserts (f x) x m) M.empty

allMap :: (Eq k, Hashable k) => (v -> Bool) -> M.HashMap k v -> Bool
allMap p = L.foldl' (\a v -> a && p v) True

hashNub :: (Eq k, Hashable k) => [k] -> [k]
hashNub = M.keys . M.fromList . fmap (, ())

sortNub :: (Ord a) => [a] -> [a]
sortNub = nubOrd . L.sort
  where
    nubOrd (x:t@(y:_))
      | x == y    = nubOrd t
      | otherwise = x : nubOrd t
    nubOrd xs     = xs

duplicates :: (Eq k, Hashable k) => [k] -> [k]
duplicates xs = [ x | (x, n) <- count xs, 1 < n ]

#ifdef MIN_VERSION_located_base
safeZip :: (?callStack :: CallStack) => String -> [a] -> [b] -> [(a,b)]
safeZipWith :: (?callStack :: CallStack) => String -> (a -> b -> c) -> [a] -> [b] -> [c]
#endif

safeZip msg xs ys
  | nxs == nys
  = zip xs ys
  | otherwise
  = errorstar $ "safeZip called on non-eq-sized lists (nxs = " ++ show nxs ++ ", nys = " ++ show nys ++ ") : " ++ msg
  where
    nxs = length xs
    nys = length ys

safeZipWith msg f xs ys
  | nxs == nys
  = zipWith f xs ys
  | otherwise
  = errorstar $ "safeZipWith called on non-eq-sized lists (nxs = " ++ show nxs ++ ", nys = " ++ show nys ++ ") : " ++ msg
    where nxs = length xs
          nys = length ys


{-@ type ListNE a = {v:[a] | 0 < len v} @-}
type ListNE a = [a]

#ifdef MIN_VERSION_located_base
safeHead   :: (?callStack :: CallStack) => String -> ListNE a -> a
safeLast   :: (?callStack :: CallStack) => String -> ListNE a -> a
safeInit   :: (?callStack :: CallStack) => String -> ListNE a -> [a]
safeUncons :: (?callStack :: CallStack) => String -> ListNE a -> (a, [a])
safeUnsnoc :: (?callStack :: CallStack) => String -> ListNE a -> ([a], a)
safeFromList :: (?callStack :: CallStack, Eq k, Hashable k, Show k) => String -> [(k, v)] -> M.HashMap k v
#else
safeHead   :: String -> ListNE a -> a
safeLast   :: String -> ListNE a -> a
safeInit   :: String -> ListNE a -> [a]
safeUncons :: String -> ListNE a -> (a, [a])
safeUnsnoc :: String -> ListNE a -> ([a], a)
safeFromList :: (Eq k, Hashable k, Show k) => String -> [(k, v)] -> M.HashMap k v
#endif

safeFromList msg kvs = applyNonNull (M.fromList kvs) err (dups kvs)
  where
    dups             = duplicates . fmap fst
    err              = errorstar . wrap "safeFromList with duplicates" msg . show
    wrap m1 m2 s     = m1 ++ " " ++ s ++ " " ++ m2

safeHead _   (x:_) = x
safeHead msg _     = errorstar $ "safeHead with empty list " ++ msg

safeLast _ xs@(_:_) = last xs
safeLast msg _      = errorstar $ "safeLast with empty list " ++ msg

safeInit _ xs@(_:_) = init xs
safeInit msg _      = errorstar $ "safeInit with empty list " ++ msg

safeUncons _ (x:xs) = (x, xs)
safeUncons msg _    = errorstar $ "safeUncons with empty list " ++ msg

safeUnsnoc msg = swap . second reverse . safeUncons msg . reverse

executeShellCommand :: String -> String -> IO ExitCode
executeShellCommand phase cmd
  = do writeLoud $ "EXEC: " ++ cmd
       bracket_ (startPhase Loud phase) (donePhase Loud phase) $ system cmd

applyNonNull :: b -> ([a] -> b) -> [a] -> b
applyNonNull def _ [] = def
applyNonNull _   f xs = f xs

arrow, dcolon :: Doc
arrow              = text "->"
dcolon             = colon <> colon

intersperse :: Doc -> [Doc] -> Doc
intersperse d ds   = hsep $ punctuate d ds

tshow :: (Show a) => a -> Doc
tshow              = text . show

-- | If loud, write a string to stdout
writeLoud :: String -> IO ()
writeLoud s = whenLoud $ putStrLn s >> hFlush stdout

ensurePath :: FilePath -> IO ()
ensurePath = createDirectoryIfMissing True . takeDirectory

singleton :: a -> [a]
singleton x = [x]

pair :: a -> a -> [a]
pair x1 x2 = [x1, x2]

triple :: a -> a -> a -> [a]
triple x1 x2 x3 = [x1, x2, x3]


fM :: (Monad m) => (a -> b) -> a -> m b
fM f = return . f

whenM :: (Monad m) => m Bool -> m () -> m ()
whenM cond act = do
  b <- cond
  when b act


mapEither :: (a -> Either b c) -> [a] -> ([b], [c])
mapEither _ []     = ([], [])
mapEither f (x:xs) = case f x of
                       Left y  -> (y:ys, zs)
                       Right z -> (ys, z:zs)
                     where
                       (ys, zs) = mapEither f xs

componentsWith :: (Ord c) => (a -> [(b, c, [c])]) -> a -> [[b]]
componentsWith eF x = map (fst3 . f) <$> vss
  where
    (g,f,_)         = G.graphFromEdges . eF $ x
    vss             = T.flatten <$> G.components g

topoSortWith :: (Ord v) => (a -> (v, [v])) -> [a] -> [a]
topoSortWith vF xs = fst3 . f <$> G.topSort g
  where
    (g, f, _)      = G.graphFromEdges es
    es             = [ (x, ux, vxs) | x <- xs, let (ux, vxs) = vF x ]

-- >>> λ> exTopo
-- >>> [1,2,4,6,5,3]
exTopo  :: [Int]
exTopo  = topoSortWith f [1,2,3,4,5,6]
  where
    f 1 = (1, [2, 3])
    f 2 = (2, [3, 4])
    f 3 = (3, []    )
    f 4 = (4, [5, 6])
    f 5 = (5, []    )
    f 6 = (6, [3]   )
    f n = (n, []    )


type EqHash a = (Eq a, Ord a, Hashable a)

-- >>> coalesce [[1], [2,1], [5], [5, 6], [5, 7], [9, 6], [10], [10,100]]
-- [[1,2],[5,7,6,9],[10,100]]

coalesce :: (EqHash v) => [ListNE v] -> [ListNE v]
coalesce = componentsWith coalesceEdges

coalesceEdges :: (EqHash v) => [ListNE v] -> [(v, v, [v])]
coalesceEdges vss = [ (u, u, vs) | (u, vs) <- groupList (uvs ++ vus) ]
  where
    vus           = swap <$> uvs
    uvs           = [ (u, v) | (u : vs) <- vss, v <- vs ]

{-
exitColorStrLn :: Moods -> String -> IO ()
exitColorStrLn c s = do
  writeIORef pbRef Nothing --(Just pr)
  putStrLn "\n"
  colorStrLn c s
-}

mapFst :: (a -> c) -> (a, b) -> (c, b)
mapFst f (x, y) = (f x, y)

mapSnd :: (b -> c) -> (a, b) -> (a, c)
mapSnd f (x, y) = (x, f y)


{-@ allCombinations :: xss:[[a]] -> [{v:[a]| len v == len xss}] @-}
allCombinations :: [[a]] -> [[a]]
allCombinations xs = assert (and . map (((length xs) == ) . length)) $ go xs
  where
   go []          = [[]]
   go [[]]        = []
   go ([]:_)      = []
   go ((x:xs):ys) = ((x:) <$> go ys) ++ go (xs:ys)

   assert b x = if b x then x else errorstar "allCombinations: assertion violation"

powerset :: [a] -> [[a]]
powerset xs = filterM (const [False, True]) xs

(=>>) :: Monad m => m b -> (b -> m a) -> m b
(=>>) m f = m >>= (\x -> f x >> return x)

(<<=) :: Monad m => (b -> m a) -> m b -> m b
(<<=) = flip (=>>)

(<$$>) ::  (Monad m) => (a -> m b) -> [a] -> m [b]
_ <$$> []           = return []
f <$$> [x1]         = singleton <$> f x1
f <$$> [x1, x2]     = pair      <$> f x1 <*> f x2
f <$$> [x1, x2, x3] = triple    <$> f x1 <*> f x2 <*> f x3
f <$$> xs           = revMapM f ({- trace msg -} xs)
  where
    _msg            = "<$$> on " ++ show (length xs)

revMapM  :: (Monad m) => (a -> m b) -> [a] -> m [b]
revMapM f          = go []
  where
    go !acc []     = return (reverse acc)
    go !acc (x:xs) = do {!y <- f x; go (y:acc) xs}
