module Gradual.GUI (render) where

import Language.Haskell.Liquid.UX.Annotate (tokeniseWithLoc)
import Language.Fixpoint.Types (KVar, Expr)
import Language.Fixpoint.Utils.Files

import Gradual.Types 
import Gradual.PrettyPrinting 
import qualified Gradual.GUI.Solution.Annotate as Sol
import Gradual.GUI.Annotate 
import Gradual.GUI.Types 
import Gradual.GUI.Misc 

import qualified Data.HashMap.Strict as M
import qualified Data.List           as L


render :: GConfig -> GSpan -> [[GSub a]] -> IO () 
render cfg gspan sols = 
  renderGradual  cfg gspan sols >>
  renderSolution cfg gspan sols 


renderSolution :: GConfig -> GSpan -> [[GSub a]] -> IO () 
renderSolution cfg gspan sols = do 
  tokens <- tokeniseWithLoc <$> readFile (gtarget cfg)
  let fname = makeSolFileName cfg
  let sol1  = mconcat (head <$> sols)
  let deps  = gSpanToDeps sol1 gspan
  let pkeys = makePKeys sols 
  let asols = accSols gspan sols 
  let src   = initSrc         deps pkeys sols 
              ++ "\n" ++ 
              initSrcSolutions asols deps pkeys sols 
  writeFile fname $! (Sol.renderHtml fname src tokens deps)
  putStrLn ("Output written in " ++ fname)



accSols :: GSpan -> [[GSub a]] -> M.HashMap KVar [(Expr, [KVar], [KVar])]
accSols gs sols = M.map sortByFreq $ M.mapWithKey complete $ M.mapWithKey go gs
  where
    go _ vs = combineFst [(e, v) | (v,_) <- vs, sol <- sols', Just (_, e) <- [M.lookup v sol]]
    sols' = concat sols 
    complete k vs = [(e, ks, (fst <$> M.lookupDefault [] k gs) L.\\ ks) | (e, ks) <- vs] 
    sortByFreq = reverse . L.sortBy (\(_, ks1, _) (_, ks2, _) -> compare (length ks1) (length ks2))

combineFst :: Eq a => [(a, b)] -> [(a, [b])]
combineFst = go [] 
  where
    go acc []         = acc
    go acc ((k,v):xs) = go ((k,(v:(snd<$>x))):acc) y
       where
          (x,y) = L.partition ((==k) . fst) xs 



renderGradual :: GConfig -> GSpan -> [[GSub a]] -> IO () 
renderGradual cfg gspan sols = do 
  tokens <- tokeniseWithLoc <$> readFile (gtarget cfg)
  let fname = makeFileName cfg
  let sol1  = mconcat (head <$> sols)
  let deps  = gSpanToDeps sol1 gspan
  let pkeys = makePKeys sols 
  let src   = initSrc deps pkeys sols 
  writeFile fname $! (renderHtml fname src tokens deps)
  putStrLn ("Output written in " ++ fname)


makeFileName :: GConfig -> String 
makeFileName cfg = extFileName Html $ gtarget cfg


makeSolFileName :: GConfig -> String 
makeSolFileName cfg = extFileName Html $ extFileName Result $ gtarget cfg

initSrcSolutions :: M.HashMap KVar [(Expr, [KVar], [KVar])] -> Dependencies v -> PKeys -> [[GSub a]] -> String 
initSrcSolutions asols deps pkeys _ = unlines
  [ initSols asols'
  , initCurrentSols (length asols')
  , initSafes deps asols'
  , initUnSafes deps asols'
  , initInPartition deps pkeys
  ]
  where
    asols' = snd <$> (reverse $ L.sortBy (\(k1,_) (k2,_) -> compare k1 k2) $ M.toList asols)


initInPartition :: Dependencies v -> PKeys -> String 
initInPartition deps pkeys = script $ concatMap go parts
  where
    go is = "inPartition.push(" ++ "[" 
              ++ L.intercalate"," (show <$> is) 
              ++ "]" ++ ");\n"

    parts   = map findP [1..maxK]
    findP i = [j | (ks, j) <- ipkeys, i `elem` ks]
    ipkeys  = zip pkeys' [1..]
    pkeys'  :: [[Int]]
    pkeys'  = map (map (fst.kVarId deps)) pkeys

    maxK    = maximumInt $ map maximumInt pkeys'

    maximumInt [] = 0 
    maximumInt xs = maximum xs 

initUnSafes :: Dependencies v -> [[(a, b, [KVar])]] -> String
initUnSafes deps xs = script $ concatMap go xs
  where
    go :: [(a, b, [KVar])] -> String
    go is = "unsafes.push(" ++ "[" 
              ++ L.intercalate "," (map go' is) 
              ++ "]" ++ ");\n"
    go' :: (a, b,[KVar]) -> String
    go' (_, _, ks) = "[" ++ L.intercalate "," (kVarContent . kVarId deps <$> ks) ++ "]"

    kVarContent (i,j) = "'content-" ++ show i ++ "-" ++ show j ++ "'" 


initSafes :: Dependencies v -> [[(a, [KVar], b)]] -> String
initSafes deps xs = script $ concatMap go xs
  where
    go :: [(a, [KVar], b)] -> String
    go is = "safes.push(" ++ "[" 
              ++ L.intercalate "," (map go' is) 
              ++ "]" ++ ");\n"
    go' :: (a, [KVar], b) -> String
    go' (_, ks, _) = "[" ++ L.intercalate "," (kVarContent . kVarId deps <$> ks) ++ "]"

    kVarContent (i,j) = "'content-" ++ show i ++ "-" ++ show j ++ "'" 


initSols :: [[(Expr, a, b)]] -> String
initSols = script . concatMap go
  where
    go xs = "sols.push(" ++ "[" 
              ++ L.intercalate "," [ show $ filter (/='\n') $ pretty e | (e,_,_)<-xs] 
              ++ "]" ++ ");\n"

initSrc :: Dependencies v -> PKeys -> [[GSub a]] -> String 
initSrc deps pkeys sols = unlines
  [ initDependents kmap 
  , initValues sols pkeys
  , initCurrentstatus pkeys
  , initDepzise deps 
  ]
  where
    kmap = map (kVarId deps) <$> pkeys

initValues :: [[GSub a]] -> PKeys -> String 
initValues sols pkeys = script $ concat $ zipWith go pkeys sols
  where
   go :: [KVar] -> [GSub a] -> String 
   go keys sols = "values.push(" ++ show (go' keys <$> sols) ++ ");\n"

   go' :: [KVar] -> GSub a -> [String] 
   go' keys sol = map (\k -> renderSol $ M.lookup k sol) keys 

   renderSol :: Maybe (a, Expr) -> String 
   renderSol Nothing  = "NA"
   renderSol (Just e) = filter (/= '\n') $ pretty $ snd e



initDependents :: [[(Int,Int)]] -> String
initDependents xs = script $ concatMap go xs
  where
    go is = "dependents.push(" ++ "[" 
              ++ L.intercalate"," [ "'content-" ++ show i ++ "-" ++ show j ++ "'" | (i,j)<-is] 
              ++ "]" ++ ");\n"

initCurrentstatus :: [a] -> String
initCurrentstatus ps = script $ 
  concat (replicate (length ps) "currentstatus.push(0);\n") 


initCurrentSols :: Int -> String
initCurrentSols i = script $ 
  concat (replicate i "curSol.push(0);\n") 

initDepzise ::  Dependencies v -> String
initDepzise deps = script $
  concatMap (\i -> "depzise.push(" ++ show i ++ ");\n") ns 
  where
    ns = map (length . snd) deps

