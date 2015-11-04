{-# LANGUAGE CPP #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE ImplicitParams            #-}

module Language.Fixpoint.Misc where

import           System.IO.Unsafe            (unsafePerformIO)
import           Control.Exception                (bracket_)
import           Data.Hashable
import           Data.IORef
import           Control.Arrow                    (second)
import           Control.Monad                    (forM_, unless)
import qualified Data.HashMap.Strict              as M
import qualified Data.List                        as L
import           Data.Tuple                       (swap)
import           Data.Maybe                       (fromMaybe)

import           Debug.Trace                      (trace)
import           System.Console.ANSI
import           System.Console.CmdArgs.Verbosity (isLoud, whenLoud)
import           System.Process                   (system)
import           System.Directory                 (createDirectoryIfMissing)
import           System.FilePath                  (takeDirectory)
import           Text.PrettyPrint.HughesPJ        hiding (first)
-- import           System.ProgressBar
import           System.IO ( hSetBuffering, BufferMode(NoBuffering), stdout, hFlush )

#ifdef MIN_VERSION_located_base
import Prelude hiding (error, undefined)
import GHC.Err.Located
import GHC.Stack
#endif


traceShow     ::  Show a => String -> a -> a
traceShow s x = trace ("\nTrace: [" ++ s ++ "] : " ++ show x)  x


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

-- withColor _ act = act
withColor c act
   = do setSGR [ SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid c]
        act
        setSGR [ Reset]

colorStrLn c       = withColor (moodColor c) . putStrLn
colorPhaseLn c msg = colorStrLn c . wrapStars .  (msg ++)
startPhase c msg   = colorPhaseLn c "START: " msg >> colorStrLn Ok " "
doneLine   c msg   = colorPhaseLn c "DONE:  " msg >> colorStrLn Ok " "

donePhase c str
  = case lines str of
      (l:ls) -> doneLine c l >> forM_ ls (colorPhaseLn c "") >> hFlush stdout
      _      -> return ()

putBlankLn = putStrLn "" >> hFlush stdout

-----------------------------------------------------------------------------------

wrap l r s = l ++ s ++ r

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

safeLookup msg k m = fromMaybe (errorstar msg) (M.lookup k m)

mfromJust _ (Just x) = x
mfromJust s Nothing  = errorstar $ "mfromJust: Nothing " ++ s

-- inserts       ::  Hashable k => k -> v -> M.HashMap k [v] -> M.HashMap k [v]
inserts k v m = M.insert k (v : M.lookupDefault [] k m) m

-- group         :: Hashable k => [(k, v)] -> M.HashMap k [v]
group         = groupBase M.empty
groupBase     = L.foldl' (\m (k, v) -> inserts k v m)

groupList     = M.toList . group

-- groupMap      :: Hashable k => (a -> k) -> [a] -> M.HashMap k [a]
groupMap f = L.foldl' (\m x -> inserts (f x) x m) M.empty

sortNub :: (Ord a) => [a] -> [a]
sortNub = nubOrd . L.sort
  where nubOrd (x:t@(y:_))
          | x == y    = nubOrd t
          | otherwise = x : nubOrd t
        nubOrd xs = xs


#ifdef MIN_VERSION_located_base
safeZip :: (?callStack :: CallStack) => String -> [a] -> [b] -> [(a,b)]
safeZipWith :: (?callStack :: CallStack) => String -> (a -> b -> c) -> [a] -> [b] -> [c]
#endif

safeZip msg xs ys
  | nxs == nys
  = zip xs ys
  | otherwise
  = errorstar $ "safeZip called on non-eq-sized lists (nxs = " ++ show nxs ++ ", nys = " ++ show nys ++ ") : " ++ msg
  where nxs = length xs
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


executeShellCommand phase cmd
  = do writeLoud $ "EXEC: " ++ cmd
       bracket_ (startPhase Loud phase) (donePhase Loud phase) $ system cmd

applyNonNull def _ [] = def
applyNonNull _   f xs = f xs


arrow              = text "->"
dcolon             = colon <> colon
intersperse d ds   = hsep $ punctuate d ds

tshow              = text . show

-- | if loud, write a string to stdout
writeLoud :: String -> IO ()
writeLoud s = whenLoud $ putStrLn s >> hFlush stdout


ensurePath :: FilePath -> IO ()
ensurePath = createDirectoryIfMissing True . takeDirectory

fM :: (Monad m) => (a -> b) -> a -> m b
fM f = return . f

{-
exitColorStrLn :: Moods -> String -> IO ()
exitColorStrLn c s = do
  writeIORef pbRef Nothing --(Just pr)
  putStrLn "\n"
  colorStrLn c s
-}
