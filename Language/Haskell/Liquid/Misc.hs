{-# LANGUAGE DeriveDataTypeable, TupleSections, NoMonomorphismRestriction, ScopedTypeVariables #-}

module Language.Haskell.Liquid.Misc where

import Data.Hashable
import qualified Control.Exception   as Ex
-- import qualified Data.HashSet        as S 
import qualified Data.HashMap.Strict as M
import qualified Data.List as L
import Control.Applicative      ((<$>))
import Control.Monad            (forM_)
import Data.Maybe               (fromJust)
import Data.List 
import Data.Maybe (catMaybes, fromMaybe)

import System.Exit
import System.Process           (system)
import Debug.Trace              (trace)
import Data.Data
import System.Console.ANSI

-----------------------------------------------------------------------------------
------------ Support for Colored Logging ------------------------------------------
-----------------------------------------------------------------------------------

data Moods = Ok | Loud | Sad | Happy | Angry 

moodColor Ok    = Black
moodColor Loud  = Blue 
moodColor Sad   = Magenta 
moodColor Happy = Green 
moodColor Angry = Red 


wrapStars msg = "\n****************************** " ++ msg ++ " *****************************"

withColor c act
  = do setSGR [ SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid c] 
       act
       setSGR [ Reset]

colorStrLn c       = withColor (moodColor c) . putStrLn 

colorPhaseLn c msg = colorStrLn c . wrapStars .  (msg ++)
startPhase c       = colorPhaseLn c "START: "
doneLine   c       = colorPhaseLn c "DONE:  "

donePhase c str 
  = case lines str of 
      (l:ls) -> doneLine c l >> forM_ ls (colorPhaseLn c "")
      _      -> return ()

-----------------------------------------------------------------------------------

data Empty = Emp deriving (Data, Typeable, Eq, Show)

unIntersperse x ys
  = case elemIndex x ys of
      Nothing -> [ys]
      Just i  -> let (y, _:ys') = splitAt i ys 
                 in (y : unIntersperse x ys')

(=>>) m f = m >>= (\x -> f x >> return x)

wrap l r s = l ++ s ++ r

repeats n  = concat . replicate n

errorstar  = error . wrap (stars ++ "\n") (stars ++ "\n") 
  where stars = repeats 3 $ wrapStars "ERROR"

findWithDefaultL f ls d = fromMaybe d (L.find f ls)

fst3 ::  (a, b, c) -> a
fst3 (x,_,_) = x

snd3 ::  (a, b, c) -> b
snd3 (_,x,_) = x

thd3 ::  (a, b, c) -> c
thd3 (_,_,x) = x


single ::  a -> [a]
single x = [x]

mapFst f (x, y)  = (f x, y)
mapSnd f (x, y)  = (x, f y)

mapFst3 f (x, y, z) = (f x, y, z)
mapSnd3 f (x, y, z) = (x, f y, z)
mapThd3 f (x, y, z) = (x, y, f z)

expandSnd = concatMap (\(xs, y) -> (, y) <$> xs)

mapPair ::  (a -> b) -> (a, a) -> (b, b)
mapPair f (x, y) = (f x, f y)

-- mlookup ::  (Show k, Hashable k) => M.HashMap k v -> k -> v
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

traceShow     ::  Show a => String -> a -> a
traceShow s x = trace ("\nTrace: [" ++ s ++ "] : " ++ show x) $ x

warnShow      ::  Show a => String -> a -> a
warnShow s x  = trace ("\nWarning: [" ++ s ++ "] : " ++ show x) $ x

-- inserts       ::  Hashable k => k -> v -> M.HashMap k [v] -> M.HashMap k [v]
inserts k v m = M.insert k (v : M.lookupDefault [] k m) m

-- group         :: Hashable k => [(k, v)] -> M.HashMap k [v]
group         = foldl' (\m (k, v) -> inserts k v m) M.empty 

-- groupMap      :: Hashable k => (a -> k) -> [a] -> M.HashMap k [a]
groupMap f xs = foldl' (\m x -> inserts (f x) x m) M.empty xs 

sortNub :: (Ord a) => [a] -> [a]
sortNub = nubOrd . sort
  where nubOrd (x:t@(y:_)) 
          | x == y    = nubOrd t 
          | otherwise = x : nubOrd t
        nubOrd xs = xs


sortDiff :: (Ord a) => [a] -> [a] -> [a]
sortDiff x1s x2s                 = go (sortNub x1s) (sortNub x2s)
  where go xs@(x:xs') ys@(y:ys') 
          | x <  y               = x : go xs' ys
          | x == y               = go xs' ys'
          | otherwise            = go xs ys'
        go xs []                 = xs
        go [] _                  = []




distinct ::  Ord a => [a] -> Bool
distinct xs = length xs == length (sortNub xs)

tr_reverse ::  [a] -> [a]
tr_reverse      = foldl' (flip (:)) []  

tr_foldr' ::  (a -> b -> b) -> b -> [a] -> b
tr_foldr' f b   = foldl' (flip f) b . tr_reverse 

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
safeFromList msg = foldl' safeAdd M.empty 
  where safeAdd m (k, v) 
          | k `M.member` m = errorstar $ msg ++ "Duplicate key " ++ show k ++ "maps to: \n" ++ (show v) ++ "\n and \n" ++ show (m M.! k)
          | otherwise      = M.insert k v m

safeUnion msg m1 m2 = 
  case Data.List.find (`M.member` m1) (M.keys m2) of
    Just k  -> errorstar $ "safeUnion with common key = " ++ show k ++ " " ++ msg
    Nothing -> M.union m1 m2

safeHead _   (x:_) = x
safeHead msg _     = errorstar $ "safeHead with empty list " ++ msg

-- memoIndex :: (Hashable b) => (a -> Maybe b) -> [a] -> [Maybe Int]
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

firstElem ::  (Eq a) => [(a, t)] -> [a] -> Maybe Int
firstElem seps str 
  = case catMaybes [ elemIndex c str | (c, _) <- seps ] of 
      [] -> Nothing
      is -> Just $ minimum is 

chopAlt ::  (Eq a) => [(a, a)] -> [a] -> [[a]]
chopAlt seps    = go 
  where go  s   = maybe [s] (go' s) (firstElem seps s)
        go' s i = let (s0, s1@(c:_)) = splitAt i s 
                      (Just c')      = lookup c seps 
                  in case elemIndex c' s1 of
                       Nothing -> [s1]
                       Just i' -> let (s2, s3) = splitAt (i' + 1) s1 in 
                                  s0 : s2 : go s3





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

stripParens ('(':xs)  = stripParens xs
stripParens xs        = stripParens' (reverse xs)
stripParens' (')':xs) = stripParens' xs
stripParens' xs       = reverse xs

ifM :: (Monad m) => m Bool -> m a -> m a -> m a
ifM bm xm ym 
  = do b <- bm
       if b then xm else ym


executeShellCommand phase cmd 
  = Ex.bracket_ (startPhase Loud phase) (donePhase Loud phase) 
    $ putStrLn ("EXEC: " ++ cmd) >> system cmd



checkExitCode _   (ExitSuccess)   = return ()
checkExitCode cmd (ExitFailure n) = errorstar $ "cmd: " ++ cmd ++ " failure code " ++ show n 

hashMapToAscList    ::  Ord a => M.HashMap a b -> [(a, b)]
hashMapToAscList    = sortBy (\x y -> compare (fst x) (fst y)) . M.toList

hashMapMapWithKey   :: (k -> v1 -> v2) -> M.HashMap k v1 -> M.HashMap k v2
hashMapMapWithKey f = fromJust . M.traverseWithKey (\k v -> Just (f k v)) 

hashMapMapKeys      :: (Eq k, Hashable k) => (t -> k) -> M.HashMap t v -> M.HashMap k v
hashMapMapKeys f    = M.fromList . fmap (mapFst f) . M.toList 

