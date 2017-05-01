-----------------------------------------------------------------------------
-- |
-- Module      :  Numeric.Chain
-- Copyright   :  (c) Vivian McPhail 2010
-- License     :  GPL-style
--
-- Maintainer  :  Vivian McPhail <haskell.vivian.mcphail <at> gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
-- optimisation of association order for chains of matrix multiplication
--
-----------------------------------------------------------------------------

module Numeric.Chain (
                      optimiseMult,
                     ) where

import Data.Maybe

import Data.Packed.Matrix
import Numeric.ContainerBoot

import qualified Data.Array.IArray as A

-----------------------------------------------------------------------------
{- | 
     Provide optimal association order for a chain of matrix multiplications 
     and apply the multiplications.

     The algorithm is the well-known O(n\^3) dynamic programming algorithm
     that builds a pyramid of optimal associations.

> m1, m2, m3, m4 :: Matrix Double
> m1 = (10><15) [1..]
> m2 = (15><20) [1..]
> m3 = (20><5) [1..]
> m4 = (5><10) [1..]

> >>> optimiseMult [m1,m2,m3,m4]

will perform @((m1 `multiply` (m2 `multiply` m3)) `multiply` m4)@

The naive left-to-right multiplication would take @4500@ scalar multiplications
whereas the optimised version performs @2750@ scalar multiplications.  The complexity
in this case is 32 (= 4^3/2) * (2 comparisons, 3 scalar multiplications, 3 scalar additions,
5 lookups, 2 updates) + a constant (= three table allocations)
-}
optimiseMult :: Product t => [Matrix t] -> Matrix t
optimiseMult = chain

-----------------------------------------------------------------------------

type Matrices a = A.Array Int (Matrix a)
type Sizes      = A.Array Int (Int,Int)
type Cost       = A.Array Int (A.Array Int (Maybe Int))
type Indexes    = A.Array Int (A.Array Int (Maybe ((Int,Int),(Int,Int))))

update :: A.Array Int (A.Array Int a) -> (Int,Int) -> a -> A.Array Int (A.Array Int a)
update a (r,c) e = a A.// [(r,(a A.! r) A.// [(c,e)])]

newWorkSpaceCost :: Int -> A.Array Int (A.Array Int (Maybe Int))
newWorkSpaceCost n = A.array (1,n) $ map (\i -> (i, subArray i)) [1..n]
   where subArray i = A.listArray (1,i) (repeat Nothing)

newWorkSpaceIndexes :: Int -> A.Array Int (A.Array Int (Maybe ((Int,Int),(Int,Int))))
newWorkSpaceIndexes n = A.array (1,n) $ map (\i -> (i, subArray i)) [1..n]
   where subArray i = A.listArray (1,i) (repeat Nothing)

matricesToSizes :: [Matrix a] -> Sizes
matricesToSizes ms = A.listArray (1,length ms) $ map (\m -> (rows m,cols m)) ms

chain :: Product a => [Matrix a] -> Matrix a
chain []  = error "chain: zero matrices to multiply"
chain [m] = m
chain [ml,mr] = ml `multiply` mr
chain ms = let ln = length ms
               ma = A.listArray (1,ln) ms
               mz = matricesToSizes ms
               i = chain_cost mz
           in chain_paren (ln,ln) i ma

chain_cost :: Sizes -> Indexes
chain_cost mz = let (_,u) = A.bounds mz
                    cost = newWorkSpaceCost u
                    ixes = newWorkSpaceIndexes u
                    (_,_,i) =  foldl chain_cost' (mz,cost,ixes) (order u)
                in i

chain_cost' :: (Sizes,Cost,Indexes) -> (Int,Int) -> (Sizes,Cost,Indexes)
chain_cost' sci@(mz,cost,ixes) (r,c) 
    | c == 1                     = let cost' = update cost (r,c) (Just 0)
                                       ixes' = update ixes (r,c) (Just ((r,c),(r,c)))
                                       in (mz,cost',ixes')
    | otherwise                  = minimum_cost sci (r,c)

minimum_cost :: (Sizes,Cost,Indexes) -> (Int,Int) -> (Sizes,Cost,Indexes)
minimum_cost sci fu = foldl (smaller_cost fu) sci (fulcrum_order fu)

smaller_cost :: (Int,Int) -> (Sizes,Cost,Indexes) -> ((Int,Int),(Int,Int)) -> (Sizes,Cost,Indexes)
smaller_cost (r,c) (mz,cost,ixes) ix@((lr,lc),(rr,rc)) = let op_cost =   fromJust ((cost A.! lr) A.! lc)
                                                                       + fromJust ((cost A.! rr) A.! rc)
                                                                       + fst (mz A.! (lr-lc+1))
                                                                         * snd (mz A.! lc)
                                                                         * snd (mz A.! rr)
                                                             cost' = (cost A.! r) A.! c
                                                         in case cost' of
                                                                       Nothing -> let cost'' = update cost (r,c) (Just op_cost)
                                                                                      ixes'' = update ixes (r,c) (Just ix)
                                                                                  in (mz,cost'',ixes'')
                                                                       Just ct -> if op_cost < ct then
                                                                                  let cost'' = update cost (r,c) (Just op_cost)
                                                                                      ixes'' = update ixes (r,c) (Just ix)
                                                                                  in (mz,cost'',ixes'')
                                                                                  else (mz,cost,ixes)
                                                                         

fulcrum_order (r,c) = let fs' = zip (repeat r) [1..(c-1)]
                      in map (partner (r,c)) fs'

partner (r,c) (a,b) = ((r-b, c-b), (a,b))

order 0 = []
order n = order (n-1) ++ zip (repeat n) [1..n]

chain_paren :: Product a => (Int,Int) -> Indexes -> Matrices a -> Matrix a
chain_paren (r,c) ixes ma = let ((lr,lc),(rr,rc)) = fromJust $ (ixes A.! r) A.! c
                            in if lr == rr && lc == rc then (ma A.! lr)
                               else (chain_paren (lr,lc) ixes ma) `multiply` (chain_paren (rr,rc) ixes ma) 

--------------------------------------------------------------------------

{- TESTS -}

-- optimal association is ((m1*(m2*m3))*m4)
m1, m2, m3, m4 :: Matrix Double
m1 = (10><15) [1..]
m2 = (15><20) [1..]
m3 = (20><5) [1..]
m4 = (5><10) [1..]