{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE FlexibleInstances         #-}

module Language.Haskell.Liquid.Strata (
    SubStratum(..)
  , solveStrata
  , (<:=)
  ) where

import Control.Applicative      ((<$>))

import Language.Fixpoint.Types (Symbol)
import Language.Haskell.Liquid.Types hiding (Def, Loc)

s1 <:= s2 
  | any (==SDiv) s1 && any (==SFin) s2 = False
  | otherwise                          = True

solveStrata = go True [] [] 
  where go False solved _   [] = solved
        go True  solved acc [] = go False solved [] $ {-traceShow ("OLD \n" ++ showMap solved acc ) $ -} subsS solved <$> acc
        go mod   solved acc (([], _):ls) = go mod solved acc ls
        go mod   solved acc ((_, []):ls) = go mod solved acc ls
        go mod   solved acc (l:ls) | allSVars l  = go mod solved (l:acc) ls
                                   | noSVar   l  = go mod solved acc ls 
                                   | noUpdate l  = go mod solved (l:acc) ls 
                                   | otherwise   = go True (solve l ++ solved) (l:acc) ls 


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

instance SubStratum (Annot SpecType) where
  subS su (AnnUse t) = AnnUse $ subS su t
  subS su (AnnDef t) = AnnDef $ subS su t
  subS su (AnnRDf t) = AnnRDf $ subS su t
  subS _  (AnnLoc s) = AnnLoc s

instance SubStratum SpecType where
  subS su t = (\r -> r {ur_strata = subS su (ur_strata r)}) <$> t


