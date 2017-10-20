{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Gradual.GUI.Types where

import Language.Haskell.HsColour.Classify (TokenType)
import Language.Haskell.Liquid.GHC.Misc   (Loc(..))

import qualified Data.HashMap.Strict       as M
import Language.Fixpoint.Types.Refinements hiding (L)
import Language.Fixpoint.Types.Spans hiding (Loc(..))
import Language.Fixpoint.Types (symbolString, Symbol) 
import qualified Data.List as L 
import qualified Data.Char as C 
import Data.Maybe (fromJust, fromMaybe)


import Gradual.Types 
import Gradual.PrettyPrinting 


data Unique  = Unique {uId :: Int, uLoc :: SrcSpan, uName :: Symbol} 
type LocTokens = [(TokenType, String, Loc)]
type Deps      = Dependencies () --  [(Int, [SrcSpan])] 
type SDeps     = Dependencies String
type Dependencies val = [(Unique, [(Unique,val)])]
type PKeys    = [[KVar]]

makePKeys :: [[GSub a]] -> PKeys 
makePKeys sols = M.keys <$> head <$> sols

instance Show Unique where
  show u = show (uLoc u)

kVarId :: Dependencies v -> KVar -> (Int, Int)
kVarId deps k = fromMaybe (0,0) $ L.lookup (kv k) 
                  [(uName x,(uId ui, uId x)) | (ui, xs) <- deps, (x,_) <- xs]

srcDeps :: Dependencies v -> [(Int, Int, SrcSpan, v)]
srcDeps deps = [(uId ui, uId x, uLoc x, v) | (ui, xs) <- deps , (x,v) <- xs]


gSpanToDeps :: GSub a -> GSpan -> SDeps 
gSpanToDeps sol gm = [(Unique i (kVarSpan $ kv k) (kv k), mapValues ks) 
                        | ((k,ks),i) <- zip gml [1..]] 
  where
    mapValues ks = [(Unique i s $ kv k, lookSol k) | ((k,Just s), i) <- zip ks [1..]]
    gml          = L.sortBy (\(k1,_) (k2,_) -> compare (kVarSpan $ kv k1) (kVarSpan $ kv k2)) 
                            $ M.toList gm
    lookSol k    = fromMaybe "NA" (pretty . snd <$> M.lookup k sol) 



kVarSpan :: Symbol -> SrcSpan
kVarSpan k = SS lc lc
  where
    L (l, c) = symbolLoc k
    fn  = takeFileName $ symbolString k
    lc = toSourcePos (fn, l, c) 

takeFileName :: String -> String 
takeFileName ('$':xs) = takeWhile (/= ' ') xs 
takeFileName _ = ""

symbolLoc :: Symbol -> Loc
symbolLoc x = L (read line, read col)
  where
    (line, rest) = spanAfter C.isDigit "line " (symbolString x)
    (col, _)     = spanAfter C.isDigit "column " rest
    spanAfter p str input = L.span p $ fromJust $ L.stripPrefix str $ 
                             head  $ filter (L.isPrefixOf str) $ L.tails input
