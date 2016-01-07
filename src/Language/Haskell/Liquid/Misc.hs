{-# LANGUAGE TupleSections             #-}

module Language.Haskell.Liquid.Misc where

import Control.Monad (liftM2)
import Control.Applicative
import Control.Arrow (first)
import System.FilePath

import           Control.Exception     (catch, IOException)
import qualified Data.HashSet          as S
import qualified Data.HashMap.Strict   as M
import qualified Data.List             as L
-- import           Data.Maybe            (fromJust)
import           Data.Maybe              -- (fromMaybe)
import           Data.Hashable
import qualified Data.ByteString       as B
import           Data.ByteString.Char8 (pack, unpack)
import           Text.PrettyPrint.HughesPJ ((<>), char)
import           Debug.Trace (trace)

import Language.Fixpoint.Misc

import Paths_liquidhaskell


(!?) :: [a] -> Int -> Maybe a
[]     !? _ = Nothing
(x:_)  !? 0 = Just x
(_:xs) !? n = xs !? (n-1)

safeFromJust _  (Just x) = x
safeFromJust err _       = errorstar err

fst4 (a,_,_,_) = a
snd4 (_,b,_,_) = b

mapFourth4 f (x, y, z, w) = (x, y, z, f w)

addFst3   a (b, c) = (a, b, c)
addThd3   c (a, b) = (a, b, c)
dropFst3 (_, x, y) = (x, y)
dropThd3 (x, y, _) = (x, y)

replaceN n y ls = [if i == n then y else x | (x, i) <- zip ls [0..]]

fourth4 (_,_,_,x) = x
third4  (_,_,x,_) = x

mapSndM :: (Applicative m) => (b -> m c) -> (a, b) -> m (a, c)
-- mapSndM f (x, y) = return . (x,) =<< f y
mapSndM f (x, y) = (x, ) <$> f y

firstM  f (a,b) = (,b) <$> f a
secondM f (a,b) = (a,) <$> f b

first3M  f (a,b,c) = (,b,c) <$> f a
second3M f (a,b,c) = (a,,c) <$> f b
third3M  f (a,b,c) = (a,b,) <$> f c

third3 f (a,b,c) = (a,b,f c)

zip4 (x1:xs1) (x2:xs2) (x3:xs3) (x4:xs4) = (x1, x2, x3, x4) : (zip4 xs1 xs2 xs3 xs4)
zip4 _ _ _ _                             = []


getIncludeDir      = dropFileName <$> getDataFileName ("include" </> "Prelude.spec")
getCssPath         = getDataFileName $ "syntax" </> "liquid.css"
getCoreToLogicPath = fmap (</> "CoreToLogic.lg") getIncludeDir


{-@ type ListN a N = {v:[a] | len v = N} @-}
{-@ type ListL a L = ListN a (len L) @-}

{-@ safeZipWithError :: _ -> xs:[a] -> ListL b xs -> ListL (a,b) xs / [xs] @-}
safeZipWithError msg (x:xs) (y:ys) = (x,y) : safeZipWithError msg xs ys
safeZipWithError _   []     []     = []
safeZipWithError msg _      _      = errorstar msg

safeZip3WithError msg (x:xs) (y:ys) (z:zs) = (x,y,z) : safeZip3WithError msg xs ys zs
safeZip3WithError _   []     []     []     = []
safeZip3WithError msg _      _      _      = errorstar msg

mapNs ns f xs = foldl (\xs n -> mapN n f xs) xs ns

mapN 0 f (x:xs) = f x : xs
mapN n f (x:xs) = x : mapN (n-1) f xs
mapN _ _ []     = []


zipWithDefM :: Monad m => (a -> a -> m a) -> [a] -> [a] -> m [a]
zipWithDefM _ []     []     = return []
zipWithDefM _ xs     []     = return xs 
zipWithDefM _ []     ys     = return ys 
zipWithDefM f (x:xs) (y:ys) = liftM2 (:) (f x y) (zipWithDefM f xs ys) 

--------------------------------------
-- Originally part of Fixpoint's Misc:
--------------------------------------

single x = [x]

mapFst f (x, y)  = (f x, y)
mapSnd f (x, y)  = (x, f y)

mapFst3 f (x, y, z) = (f x, y, z)
mapSnd3 f (x, y, z) = (x, f y, z)
mapThd3 f (x, y, z) = (x, y, f z)


hashMapMapWithKey   :: (k -> v1 -> v2) -> M.HashMap k v1 -> M.HashMap k v2
hashMapMapWithKey f = fromJust . M.traverseWithKey (\k v -> Just (f k v))

hashMapMapKeys      :: (Eq k, Hashable k) => (t -> k) -> M.HashMap t v -> M.HashMap k v
hashMapMapKeys f    = M.fromList . fmap (first f) . M.toList

concatMapM f = fmap concat . mapM f

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
    go  s               = maybe [s] go' (firstElems seps s)
    go' (_,c',(s0, s1)) = if (B.length s2 == B.length s1) then [B.concat [s0,s1]] else (s0 : s2' : go s3')
                          where (s2, s3) = B.breakSubstring c' s1
                                s2'      = B.append s2 c'
                                s3'      = B.drop (B.length c') s3

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

angleBrackets p    = char '<' <> p <> char '>'

mkGraph :: (Eq a, Eq b, Hashable a, Hashable b) => [(a, b)] -> M.HashMap a (S.HashSet b)
mkGraph = fmap S.fromList . group

tryIgnore :: String -> IO () -> IO ()
tryIgnore s a = catch a $ \e ->
                do let err = show (e :: IOException)
                   writeLoud ("Warning: Couldn't do " ++ s ++ ": " ++ err)
                   return ()

(=>>) m f = m >>= (\x -> f x >> return x)


firstJust :: (a -> Maybe b) -> [a] -> Maybe b
firstJust f xs = listToMaybe $ catMaybes $ map f xs
