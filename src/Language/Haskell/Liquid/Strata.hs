{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE FlexibleInstances         #-}

module Language.Haskell.Liquid.Strata (
    SubStratum(..)
  , solveStrata
  ) where

import Control.Applicative      ((<$>))

import Debug.Trace (trace)
import Language.Fixpoint.Misc
import Language.Fixpoint.Types (Symbol)
import Language.Haskell.Liquid.Types hiding (Def, Loc)
import Language.Haskell.Liquid.Annotate (Annot(..))

solveStrata = go True [] [] 
  where go False solved acc [] = solved
        go True  solved acc [] = go False solved [] $ {-traceShow ("OLD \n" ++ showMap solved acc ) $ -} subsS solved <$> acc
        go mod   solved acc (([], _):ls) = go mod solved acc ls
        go mod   solved acc ((_, []):ls) = go mod solved acc ls
        go mod   solved acc (l:ls) | allSVars l  = go mod solved (l:acc) ls
                                   | noSVar   l  = go mod solved acc ls 
                                   | noUpdate l  = go mod solved (l:acc) ls 
                                   | otherwise   = go True (solve l ++ solved) (l:acc) ls 

traceSMap s init sol= sol -- trace (s ++ "\n" ++ showMap sol init) sol 

showMap :: [(Symbol, Stratum)] -> [([Stratum], [Stratum])] -> String
showMap s acc 
  = "\nMap lenght = " ++ show (length acc) ++ "\n" ++
    "Solved = (" ++ show (length s) ++ ")\n" ++ show s ++ "\n"
    ++ concatMap (\xs -> (show xs ++ "\n") ) acc ++ "\n\n"

allSVars (xs, ys) = all isSVar $ xs ++ ys
noSVar   (xs, ys) = all (not . isSVar) (xs ++ ys)
noUpdate (xs, ys) = (not $ updateFin(xs, ys)) && (not $ updateDiv (xs, ys)) 

updateFin (xs, ys) = any (==SFin) ys && any isSVar   xs
updateDiv (xs, ys) = any isSVar   ys && any (==SDiv) xs

solve (xs, ys) 
  | any (== SDiv) xs = [(l, SDiv) | SVar l <- ys] 
  | any (== SFin) ys = [(l, SFin) | SVar l <- xs] 
  | otherwise        = []


class SubStratum a where
  subS  :: (Symbol, Stratum) -> a -> a
  subsS :: [(Symbol, Stratum)] -> a -> a

  subsS su x = foldr subS x su

instance SubStratum Stratum where
  subS (x, s) (SVar y) | x == y    = s
                       | otherwise = (SVar y)
  subS _      s        = s


instance (SubStratum a, SubStratum b) => SubStratum (a, b) where
  subS su (x, y) = (subS su x, subS su y)

instance (SubStratum a) => SubStratum [a] where
  subS su xs = subS su <$> xs

instance SubStratum Annot where
  subS su (Use t) = Use $ subS su t
  subS su (Def t) = Def $ subS su t
  subS su (RDf t) = RDf $ subS su t
  subS su (Loc s) = Loc s

instance SubStratum SpecType where
  subS su t = (\r -> r {ur_strata = subS su (ur_strata r)}) <$> t


