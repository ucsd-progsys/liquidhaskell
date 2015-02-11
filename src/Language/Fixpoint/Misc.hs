{-# LANGUAGE DeriveDataTypeable, TupleSections, NoMonomorphismRestriction, ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Fixpoint.Misc where

import Data.Traversable               (traverse)
import Data.Hashable
import qualified Control.Exception     as Ex
-- import qualified Data.HashSet        as S 
import qualified Data.HashMap.Strict   as M
import qualified Data.List             as L
import qualified Data.ByteString       as B
import qualified Data.Text             as T
import Data.ByteString.Char8    (pack, unpack)
import Control.Applicative      ((<$>))
import Control.Monad            (forM_, (>=>))
import Data.Maybe               (fromJust)
import Data.Maybe               (catMaybes, fromMaybe)

import System.Exit
import System.Process           (system)
import Debug.Trace              (trace)
import Data.Data
import System.Console.ANSI
import System.Console.CmdArgs.Verbosity (whenLoud)

import Text.PrettyPrint.HughesPJ

-----------------------------------------------------------------------------------
------------ Support for Colored Logging ------------------------------------------
-----------------------------------------------------------------------------------

data Moods = Ok | Loud | Sad | Happy | Angry 

moodColor Ok    = Blue -- Black
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

unIntersperse x ys
  = case L.elemIndex x ys of
      Nothing -> [ys]
      Just i  -> let (y, _:ys') = splitAt i ys 
                 in (y : unIntersperse x ys')

(=>>) m f = m >>= (\x -> f x >> return x)

wrap l r s = l ++ s ++ r

repeats n  = concat . replicate n

errorstar  = error . wrap (stars ++ "\n") (stars ++ "\n") 
  where 
    stars = repeats 3 $ wrapStars "ERROR"

errortext  = errorstar . render 

putDocLn :: Doc -> IO ()
putDocLn = putStrLn . render 

assertstar _   True  x = x
assertstar msg False x = errorstar msg 

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
boxStrCat sep = ("[" ++) . (++ "]") . L.intercalate sep 

tryIgnore :: String -> IO () -> IO ()
tryIgnore s a = Ex.catch a $ \e -> 
                do let err = show (e :: Ex.IOException)
                   whenLoud $ putStrLn ("Warning: Couldn't do " ++ s ++ ": " ++ err)
                   return ()

traceShow     ::  Show a => String -> a -> a
traceShow s x = trace ("\nTrace: [" ++ s ++ "] : " ++ show x) $ x

warnShow      ::  Show a => String -> a -> a
warnShow s x  = trace ("\nWarning: [" ++ s ++ "] : " ++ show x) $ x

-- inserts       ::  Hashable k => k -> v -> M.HashMap k [v] -> M.HashMap k [v]
inserts k v m = M.insert k (v : M.lookupDefault [] k m) m

concatMaps    = fmap sortNub . L.foldl' (M.unionWith (++)) M.empty 

-- group         :: Hashable k => [(k, v)] -> M.HashMap k [v]
group         = L.foldl' (\m (k, v) -> inserts k v m) M.empty 

groupList     = M.toList . group

-- groupMap      :: Hashable k => (a -> k) -> [a] -> M.HashMap k [a]
groupMap f xs = L.foldl' (\m x -> inserts (f x) x m) M.empty xs 

sortNub :: (Ord a) => [a] -> [a]
sortNub = nubOrd . L.sort
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
tr_reverse      = L.foldl' (flip (:)) []  

tr_foldr' ::  (a -> b -> b) -> b -> [a] -> b
tr_foldr' f b   = L.foldl' (flip f) b . tr_reverse 

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

safeHead _   (x:_) = x
safeHead msg _     = errorstar $ "safeHead with empty list " ++ msg

safeLast _ xs@(_:_) = last xs
safeLast msg _      = errorstar $ "safeLast with empty list " ++ msg

safeInit _ xs@(_:_) = init xs
safeInit msg _      = errorstar $ "safeInit with empty list " ++ msg


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

chopPrefix p xs 
  | p `L.isPrefixOf` xs
  = Just $ drop (length p) xs
  | otherwise 
  = Nothing

firstElem ::  (Eq a) => [(a, t)] -> [a] -> Maybe Int
firstElem seps str 
  = case catMaybes [ L.elemIndex c str | (c, _) <- seps ] of 
      [] -> Nothing
      is -> Just $ minimum is 

chopAlt ::  (Eq a) => [(a, a)] -> [a] -> [[a]]
chopAlt seps    = go 
  where go  s   = maybe [s] (go' s) (firstElem seps s)
        go' s i = let (s0, s1@(c:_)) = splitAt i s 
                      (Just c')      = lookup c seps 
                  in case L.elemIndex c' s1 of
                       Nothing -> [s1]
                       Just i' -> let (s2, s3) = splitAt (i' + 1) s1 in 
                                  s0 : s2 : go s3

firstElems ::  [(B.ByteString, B.ByteString)] -> B.ByteString -> Maybe (Int, B.ByteString, (B.ByteString, B.ByteString))
firstElems seps str 
  = case splitters seps str of 
      [] -> Nothing
      is -> Just $ L.minimumBy (\x y -> compare (fst3 x) (fst3 y)) is 

splitters seps str 
  = [(i, c', z) | (c, c') <- seps
                , let z   = B.breakSubstring c str
                , let i   = B.length (fst z)
                , i < B.length str                 ]


bchopAlts :: [(B.ByteString, B.ByteString)] -> B.ByteString -> [B.ByteString]
bchopAlts seps  = go 
  where 
    go  s                 = maybe [s] (go' s) (firstElems seps s)
    go' s (i,c',(s0, s1)) = if (B.length s2 == B.length s1) then [B.concat [s0,s1]] else (s0 : s2' : go s3')
                            where (s2, s3) = B.breakSubstring c' s1
                                  s2'      = B.append s2 c'
                                  s3'      = B.drop (B.length c') s3 

chopAlts seps str = unpack <$> bchopAlts [(pack c, pack c') | (c, c') <- seps] (pack str)

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

stripParens :: T.Text -> T.Text
stripParens t = fromMaybe t (strip t)
  where
    strip = T.stripPrefix "(" >=> T.stripSuffix ")"

ifM :: (Monad m) => m Bool -> m a -> m a -> m a
ifM bm xm ym 
  = do b <- bm
       if b then xm else ym

executeShellCommand phase cmd 
  = do whenLoud $ putStrLn $ "EXEC: " ++ cmd 
       Ex.bracket_ (startPhase Loud phase) (donePhase Loud phase) $ system cmd

executeShellCommandWithOptStars v phase cmd 
  = do whenLoud $ putStrLn $ "EXEC: " ++ cmd 
       Ex.bracket_ (startPhaseWithOptStars v Loud phase) (donePhaseWithOptStars v Loud phase) $ system cmd

checkExitCode _   (ExitSuccess)   = return ()
checkExitCode cmd (ExitFailure n) = errorstar $ "cmd: " ++ cmd ++ " failure code " ++ show n 

hashMapToAscList    ::  Ord a => M.HashMap a b -> [(a, b)]
hashMapToAscList    = L.sortBy (\x y -> compare (fst x) (fst y)) . M.toList

hashMapMapWithKey   :: (k -> v1 -> v2) -> M.HashMap k v1 -> M.HashMap k v2
hashMapMapWithKey f = fromJust . M.traverseWithKey (\k v -> Just (f k v)) 

hashMapMapKeys      :: (Eq k, Hashable k) => (t -> k) -> M.HashMap t v -> M.HashMap k v
hashMapMapKeys f    = M.fromList . fmap (mapFst f) . M.toList 


applyNonNull def _ [] = def
applyNonNull _   f xs = f xs

concatMapM f = fmap concat . mapM f 



angleBrackets p    = char '<' <> p <> char '>'
dot                = char '.'
arrow              = text "->"
dcolon             = colon <> colon
intersperse d ds   = hsep $ punctuate d ds

tshow              = text . show

foldlMap           :: (a -> b -> (c, a)) -> a -> [b] -> ([c], a)
foldlMap f b xs    = (reverse zs, res)
  where 
    (zs, res)      = L.foldl' ff ([], b) xs
    ff (ys, acc) x = let (y, acc') = f acc x in (y:ys, acc')

mapEither           :: (a -> Either b c) -> [a] -> ([b], [c])
mapEither f         = go [] [] 
  where 
    go ls rs []     = (reverse ls, reverse rs)
    go ls rs (x:xs) = case f x of
                        Left l  -> go (l:ls) rs  xs
                        Right r -> go ls  (r:rs) xs

f <$$> x = traverse f x
