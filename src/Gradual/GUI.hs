module Gradual.GUI (render) where

import Language.Haskell.Liquid.UX.Annotate (tokeniseWithLoc)
import Language.Fixpoint.Types (KVar, Expr)
import Language.Fixpoint.Utils.Files

import Gradual.Types 
import Gradual.PrettyPrinting 
import Gradual.GUI.Annotate 
import Gradual.GUI.Types 
import Gradual.GUI.Misc 

import qualified Data.HashMap.Strict as M

render :: GConfig -> GSpan -> [[GSub a]] -> IO () 
render cfg gspan sols = do 
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
   renderSol (Just e) = pretty $ snd e

initDependents :: [[(Int,Int)]] -> String
initDependents xs = script $ concatMap go xs
  where
    go is = "dependents.push(" ++ "[" 
              ++ concat [ "'content-" ++ show i ++ "-" ++ show j ++ "'" | (i,j)<-is] 
              ++ "]" ++ ");\n"

initCurrentstatus :: [a] -> String
initCurrentstatus ps = script $ 
  concat (replicate (length ps) "currentstatus.push(0);\n") 


initDepzise ::  Dependencies v -> String
initDepzise deps = script $
  concatMap (\i -> "depzise.push(" ++ show i ++ ");\n") ns 
  where
    ns = map (length . snd) deps

