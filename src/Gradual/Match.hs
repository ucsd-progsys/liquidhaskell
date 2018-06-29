module Gradual.Match (matchSolutions) where

import Gradual.Types
import Gradual.PrettyPrinting
import Gradual.Misc

-- import Language.Fixpoint.Types
-- import Language.Fixpoint.Misc (traceShow)

import qualified Data.HashMap.Strict as M
import qualified Data.List           as L
import Data.Maybe (catMaybes, fromJust)


matchSolutions :: GSpan -> [[GSub a]] -> [GSub ()]
matchSolutions _ sols 
  | any null sols = []
matchSolutions gs sols = {- traceShow (concatMap (showPartition gs) sols ++ "\n" ++ concatMap prettyGSub ss) -}  ss 
  where ss = L.nub $ mergeSolutions gs sols
  -- putStrLn ("Solutions =" ++ concat (map (showPartition gs) sols))
  -- putStrLn ("MSolutions =" ++ concatMap prettyGSub (mergeSolutions gs sols))
  -- return $ M.map (\_ -> ((),[])) gs 


mergeSolutions :: GSpan -> [[GSub a]] -> [GSub ()]
mergeSolutions gs sols 
  = catMaybes $ map (unionSolutions . map (mergeSolution gs)) 
                (allCombinations sols)


unionSolutions :: [Maybe (GSub ())] -> Maybe (GSub ())
unionSolutions [] = Just mempty
unionSolutions xs = foldl1 unionMSol xs


unionMSol :: Maybe (GSub ()) -> Maybe (GSub ()) -> Maybe (GSub ()) 
unionMSol Nothing _ = Nothing
unionMSol _ Nothing = Nothing
unionMSol (Just x) (Just y) = unionSol x y 


unionSol :: GSub () -> GSub () -> Maybe (GSub ()) 
unionSol x1 x2 = if (Nothing `elem` M.elems res) then Nothing else Just (M.map fromJust res) 
  where
    res = M.unionWith (\(Just e1) (Just e2) -> if e1 == e2 then Just e1 else Nothing) 
                      (M.map Just x1) (M.map Just x2) 

_showPartition :: GSpan -> [GSub a] -> String 
_showPartition gs ss = "\nPartition:\n" ++ concat (map (showSolutions gs) ss) ++ "\n\n"

showSolutions :: GSpan -> GSub a -> String 
showSolutions gs xs = 
   unlines [ pretty k ++ ":=" ++ pretty e | (k, (_,e)) <- M.toList xs] ++ "\n"
   ++ pretty ((\m -> [(k,e) | (k, (_,e)) <- M.toList m]) <$> mergeSolution gs xs)


_prettyGSub :: (GSub a) -> String
_prettyGSub m = pretty [(k,e) | (k, (_,e)) <- M.toList m]

mergeSolution :: GSpan -> GSub a -> Maybe (GSub ()) 
mergeSolution gs sub = go [] $ map (\k -> (k, mergeKey k)) (M.keys gs)
   where
     mergeKey k = listToSSol $ map snd $ catMaybes $ map (`M.lookup` sub) (fst <$> M.lookupDefault [] k gs) 

     go acc []               = Just $ M.fromList acc 
     go _   ((_, SFail):_)   = Nothing 
     go acc ((k, SSol e):xs) = go ((k, ((), e)):acc) xs
     go acc ((_, SNA):xs)    = go acc xs 


data SSol a = SSol a | SFail | SNA deriving (Show)

listToSSol :: (Show a, Eq a) => [a] -> SSol a 
listToSSol [] = SNA 
listToSSol (x:xs) 
  | all (==x) xs 
  = SSol x 
listToSSol _ 
  = SFail
