module Graphs where

import qualified Data.Set as S
import qualified Data.Map as M
import Text.Printf

import Data.List (intercalate, sort, foldl')

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

-- preStar :: Graph -> [Int] -> Graph



