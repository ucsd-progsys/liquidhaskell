{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE ImplicitParams            #-}

module Language.Fixpoint.Misc where

import           Control.Exception                (catch, IOException, bracket_)
import           Data.Hashable
import           Data.Traversable                 (traverse)
import qualified Data.HashSet                     as S
import           Control.Applicative              ((<$>))
import           Control.Arrow                    (first, second)
import           Control.Monad                    (forM_, (>=>))
import qualified Data.HashMap.Strict              as M
import qualified Data.List                        as L
import           Data.Tuple                       (swap)
import           Data.Maybe                       (fromJust, catMaybes, fromMaybe)
import qualified Data.Text                        as T

import           Data.Data                        (Data, Typeable)
import           Debug.Trace                      (trace)
import           System.Console.ANSI
import           System.Console.CmdArgs.Verbosity (whenLoud)
import           System.Exit                      (ExitCode (..))
import           System.Process                   (system)

import           Text.PrettyPrint.HughesPJ        hiding (first)

#ifdef MIN_VERSION_located_base
import Prelude hiding (error, undefined)
import GHC.Err.Located
import GHC.Stack
#endif


-----------------------------------------------------------------------------------
------------ Support for Colored Logging ------------------------------------------
-----------------------------------------------------------------------------------

data Moods = Ok | Loud | Sad | Happy | Angry

moodColor Ok    = Black
moodColor Loud  = Blue
moodColor Sad   = Magenta
moodColor Happy = Green
moodColor Angry = Red

wrapStars msg = "\n**** " ++ msg ++ " " ++ replicate (74 - length msg) '*'

wrapStarsWithOptStars True  msg = "\n**** " ++ msg ++ " " ++ replicate (74 - length msg) '*'
wrapStarsWithOptStars False msg = wrapStars msg

-- withColor _ act = act
withColor c act
   = do setSGR [ SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid c]
        act
        setSGR [ Reset]

colorStrLn c       = withColor (moodColor c) . putStrLn
colorPhaseLn c msg = colorStrLn c . wrapStars .  (msg ++)
startPhase c msg   = colorPhaseLn c "START: " msg >> colorStrLn Ok " "
doneLine   c msg   = colorPhaseLn c "DONE:  " msg >> colorStrLn Ok " "

colorPhaseLnWithOptStars v c msg = colorStrLn c . wrapStarsWithOptStars v .  (msg ++)
startPhaseWithOptStars   v c msg = colorPhaseLnWithOptStars v c "START: " msg >> colorStrLn Ok " "
doneLineWithOptStars     v c msg = colorPhaseLnWithOptStars v c "DONE:  " msg >> colorStrLn Ok " "

donePhase c str
  = case lines str of
      (l:ls) -> doneLine c l >> forM_ ls (colorPhaseLn c "")
      _      -> return ()

donePhaseWithOptStars v c str
  = case lines str of
      (l:ls) -> doneLineWithOptStars v c l >> forM_ ls (colorPhaseLnWithOptStars v c "")
      _      -> return ()


-----------------------------------------------------------------------------------

data Empty = Emp deriving (Data, Typeable, Eq, Show)

(=>>) m f = m >>= (\x -> f x >> return x)

wrap l r s = l ++ s ++ r

repeats n  = concat . replicate n

#ifdef MIN_VERSION_located_base
errorstar :: (?callStack :: CallStack) => String -> a
#endif

errorstar  = error . wrap (stars ++ "\n") (stars ++ "\n")
  where
    stars = repeats 3 $ wrapStars "ERROR"

findWithDefaultL f ls d = fromMaybe d (L.find f ls)

fst3 ::  (a, b, c) -> a
fst3 (x,_,_) = x

snd3 ::  (a, b, c) -> b
snd3 (_,x,_) = x

thd3 ::  (a, b, c) -> c
thd3 (_,_,x) = x

#ifdef MIN_VERSION_located_base
mlookup    :: (?callStack :: CallStack, Eq k, Show k, Hashable k) => M.HashMap k v -> k -> v
safeLookup :: (?callStack :: CallStack, Eq k, Hashable k) => String -> k -> M.HashMap k v -> v
mfromJust  :: (?callStack :: CallStack) => String -> Maybe a -> a
#else
mlookup    :: (Eq k, Show k, Hashable k) => M.HashMap k v -> k -> v
safeLookup :: (Eq k, Hashable k) => String -> k -> M.HashMap k v -> v
mfromJust  :: String -> Maybe a -> a
#endif

mlookup m k = case M.lookup k m of
                Just v  -> v
                Nothing -> errorstar $ "mlookup: unknown key " ++ show k

safeLookup msg k m = fromMaybe (errorstar msg) (M.lookup k m)

mfromJust _ (Just x) = x
mfromJust s Nothing  = errorstar $ "mfromJust: Nothing " ++ s

boxStrCat ::  String -> [String] -> String
boxStrCat sep = ("[" ++) . (++ "]") . L.intercalate sep

tryIgnore :: String -> IO () -> IO ()
tryIgnore s a = catch a $ \e ->
                do let err = show (e :: IOException)
                   writeLoud ("Warning: Couldn't do " ++ s ++ ": " ++ err)
                   return ()

traceShow     ::  Show a => String -> a -> a
traceShow s x = trace ("\nTrace: [" ++ s ++ "] : " ++ show x)  x

warnShow      ::  Show a => String -> a -> a
warnShow s x  = trace ("\nWarning: [" ++ s ++ "] : " ++ show x)  x

-- inserts       ::  Hashable k => k -> v -> M.HashMap k [v] -> M.HashMap k [v]
inserts k v m = M.insert k (v : M.lookupDefault [] k m) m

-- | Version of inserts that handles Maybe keys. If the key is
-- Nothing, the value is not inserted
maybeInserts Nothing _ m = m
maybeInserts (Just k) v m = inserts k v m

concatMaps    = fmap sortNub . L.foldl' (M.unionWith (++)) M.empty

-- group         :: Hashable k => [(k, v)] -> M.HashMap k [v]
group         = groupBase M.empty
groupBase     = L.foldl' (\m (k, v) -> inserts k v m)

groupList     = M.toList . group

groupFun :: (Show k, Eq k, Hashable k) => M.HashMap k Int -> k -> Int
groupFun m k = safeLookup ("groupFun: " ++ show k) k m

mkGraph :: (Eq a, Eq b, Hashable a, Hashable b) => [(a, b)] -> M.HashMap a (S.HashSet b)
mkGraph = fmap S.fromList . group


-- groupMap      :: Hashable k => (a -> k) -> [a] -> M.HashMap k [a]
groupMap f = L.foldl' (\m x -> inserts (f x) x m) M.empty

maybeGroupMap f = L.foldl' (\m x -> maybeInserts (f x) x m) M.empty

sortNub :: (Ord a) => [a] -> [a]
sortNub = nubOrd . L.sort
  where nubOrd (x:t@(y:_))
          | x == y    = nubOrd t
          | otherwise = x : nubOrd t
        nubOrd xs = xs



distinct ::  Ord a => [a] -> Bool
distinct xs = length xs == length (sortNub xs)

tr_reverse ::  [a] -> [a]
tr_reverse      = L.foldl' (flip (:)) []

tr_foldr' ::  (a -> b -> b) -> b -> [a] -> b
tr_foldr' f b   = L.foldl' (flip f) b . tr_reverse

#ifdef MIN_VERSION_located_base
safeZip :: (?callStack :: CallStack) => String -> [a] -> [b] -> [(a,b)]
safeZipWith :: (?callStack :: CallStack) => String -> (a -> b -> c) -> [a] -> [b] -> [c]
safeFromList :: (?callStack :: CallStack, Hashable k, Eq k, Show k, Show a) => String -> [(k, a)] -> M.HashMap k a
safeUnion :: (?callStack :: CallStack, Hashable k, Eq k, Show k, Show a)
          => String -> M.HashMap k a -> M.HashMap k a -> M.HashMap k a
#endif

safeZip msg xs ys
  | nxs == nys
  = zip xs ys
  | otherwise
  = errorstar $ "safeZip called on non-eq-sized lists (nxs = " ++ show nxs ++ ", nys = " ++ show nys ++ ") : " ++ msg
  where nxs = length xs
        nys = length ys

-- eqLen = on (==) length

safeZipWith msg f xs ys
  | nxs == nys
  = zipWith f xs ys
  | otherwise
  = errorstar $ "safeZipWith called on non-eq-sized lists (nxs = " ++ show nxs ++ ", nys = " ++ show nys ++ ") : " ++ msg
    where nxs = length xs
          nys = length ys

-- safe0ZipWith msg f xs ys
--   | length xs == length ys
--   = zipWith f xs ys
-- safe0ZipWith _ _ [] _
--   = []
-- safe0ZipWith _ _ _ []
--   = []
-- safe0ZipWith msg _ xs ys
--   = errorstar $ "safeZipWith called on non-eq-sized lists (nxs = " ++ show nxs ++ ", nys = " ++ show nys ++ ") : " ++ msg
--     where nxs = length xs
--           nys = length ys


-- safeFromList :: (Hashable k, Show k, Show a) => String -> [(k, a)] -> M.HashMap k a
safeFromList msg = L.foldl' safeAdd M.empty
  where safeAdd m (k, v)
          | k `M.member` m = errorstar $ msg ++ "Duplicate key " ++ show k ++ "maps to: \n" ++ (show v) ++ "\n and \n" ++ show (m M.! k)
          | otherwise      = M.insert k v m

safeUnion msg m1 m2 =
  case L.find (`M.member` m1) (M.keys m2) of
    Just k  -> errorstar $ "safeUnion with common key = " ++ show k ++ " " ++ msg
    Nothing -> M.union m1 m2

{-@ type ListNE a = {v:[a] | 0 < len v} @-}
type ListNE a = [a]

#ifdef MIN_VERSION_located_base
safeHead   :: (?callStack :: CallStack) => String -> ListNE a -> a
safeLast   :: (?callStack :: CallStack) => String -> ListNE a -> a
safeInit   :: (?callStack :: CallStack) => String -> ListNE a -> [a]
safeUncons :: (?callStack :: CallStack) => String -> ListNE a -> (a, [a])
safeUnsnoc :: (?callStack :: CallStack) => String -> ListNE a -> ([a], a)
#else
safeHead   :: String -> ListNE a -> a
safeLast   :: String -> ListNE a -> a
safeInit   :: String -> ListNE a -> [a]
safeUncons :: String -> ListNE a -> (a, [a])
safeUnsnoc :: String -> ListNE a -> ([a], a)
#endif

safeHead _   (x:_) = x
safeHead msg _     = errorstar $ "safeHead with empty list " ++ msg

safeLast _ xs@(_:_) = last xs
safeLast msg _      = errorstar $ "safeLast with empty list " ++ msg


safeInit _ xs@(_:_) = init xs
safeInit msg _      = errorstar $ "safeInit with empty list " ++ msg

safeUncons _ (x:xs) = (x, xs)
safeUncons msg _    = errorstar $ "safeUncons with empty list " ++ msg

safeUnsnoc msg = swap . second reverse . safeUncons msg . reverse



-- memoIndex :: (Hashable b) => (a -> Maybe b) -> [a] -> [Maybe Int]
memoIndex f = snd . L.mapAccumL foo M.empty
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
  = case L.findIndex f xs of
      Just n  -> take n xs
      Nothing -> xs

firstElem ::  (Eq a) => [(a, t)] -> [a] -> Maybe Int
firstElem seps str
  = case catMaybes [ L.elemIndex c str | (c, _) <- seps ] of
      [] -> Nothing
      is -> Just $ minimum is

findFirst ::  Monad m => (t -> m [a]) -> [t] -> m (Maybe a)
findFirst _ []     = return Nothing
findFirst f (x:xs) = do r <- f x
                        case r of
                          y:_ -> return (Just y)
                          []  -> findFirst f xs

testM f x = do b <- f x
               return $ if b then [x] else []

-- unions :: (Hashable a) => [S.HashSet a] -> S.HashSet a
-- unions = foldl' S.union S.empty
-- Just S.unions!

executeShellCommand phase cmd
  = do writeLoud $ "EXEC: " ++ cmd
       bracket_ (startPhase Loud phase) (donePhase Loud phase) $ system cmd

executeShellCommandWithOptStars v phase cmd
  = do writeLoud $ "EXEC: " ++ cmd
       bracket_ (startPhaseWithOptStars v Loud phase) (donePhaseWithOptStars v Loud phase) $ system cmd

checkExitCode _   (ExitSuccess)   = return ()
checkExitCode cmd (ExitFailure n) = errorstar $ "cmd: " ++ cmd ++ " failure code " ++ show n


applyNonNull def _ [] = def
applyNonNull _   f xs = f xs


angleBrackets p    = char '<' <> p <> char '>'
dot                = char '.'
arrow              = text "->"
dcolon             = colon <> colon
intersperse d ds   = hsep $ punctuate d ds

tshow              = text . show

f <$$> x = traverse f x

-- | if loud, write a string to stdout
writeLoud :: String -> IO ()
writeLoud = whenLoud . putStrLn
