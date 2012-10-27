module Graphs where

import qualified Data.Set as S
import qualified Data.Map as M
import Text.Printf
import Data.Foldable (find)
import Data.List (intercalate, sort, sortBy, foldl', nubBy)

type Graph = M.Map Int [Int]

ofList :: [(Int, Int)] -> Graph
ofList uvs = sort `fmap` foldl' adds M.empty uvs
  where adds g (u, v) = M.insert u (v: (M.findWithDefault [] u g)) g

readGraph :: FilePath -> IO Graph
readGraph f 
  = do s     <- readFile f
       let es = filter ((4 ==) . length) (words `fmap` lines s)
       return $ ofList [((read u) :: Int, (read v) :: Int) | [u,_,v,_] <- es]
  
writeGraph :: FilePath -> Graph -> IO ()
writeGraph f = writeFile f . showGraph 

showGraph :: Graph -> String
showGraph g  = intercalate "\n" [ printf "%d -> %d ;" u v | (u, vs) <- M.toList g, v <- vs] 

postStar :: Graph -> S.Set Int -> Graph
postStar g vs = go vs S.empty
  where 
    go new reach
      | S.null new = project reach g
      | otherwise  = let vs'    = posts g new 
                         reach' = S.union reach new
                         new'   = S.difference vs' reach' 
                     in go new' reach'

project :: S.Set Int -> Graph -> Graph
project reach = M.map (filter (`S.member` reach)) . M.filterWithKey (\u _ -> S.member u reach)

posts      :: Graph -> S.Set Int -> S.Set Int 
posts g us = S.unions [post g u | u <- S.toList us]  

post     :: Graph -> Int -> S.Set Int 
post g u = S.fromList $ M.findWithDefault [] u g


findPath :: Graph -> Int -> Int -> Maybe [Int]
findPath g src dst = go M.empty (M.fromList [(src, [])]) 
  where 
    go :: M.Map Int [Int] -> M.Map Int [Int] -> Maybe [Int]
    go reach frnt 
      | M.null frnt = Nothing 
      | otherwise   = case find ((dst ==) . fst) (M.assocs frnt) of
                        Just (_, path) -> Just (reverse path)
                        Nothing        -> let reach' = updReach reach frnt -- (S.fromList $ fst `fmap` S.elems frnt) 
                                              frnt'  = postFront g reach frnt
                                        in go reach' frnt'
   
updReach = M.unionWith  (\p1 p2 -> if length p1 < length p2 then p1 else p2)

postFront g reach frnt 
  = M.fromList 
  $ nubBy (\x y -> fst x == fst y) 
  $ sortBy (\x y -> let m = length . snd in compare (m x) (m y))
      [ (v, u:path) | (u, path) <- M.assocs frnt
                    , v         <- S.elems (post g u)
                    , not (M.member v reach) 
      ]

