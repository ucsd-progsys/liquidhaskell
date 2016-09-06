{-
NV TODO 
1. refine data type
2. complete todos
3. connect it with Steps 1 & 2
-}



{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs               #-}


{-@ LIQUID "--higherorder"       @-}
{-@ LIQUID "--totality"          @-}
{-@ LIQUID "--exactdc"           @-}

module Main where

import Language.Haskell.Liquid.String
import GHC.TypeLits
import Data.String hiding (fromString)
import Data.Proxy 
import Prelude hiding (mempty, mappend, id, mconcat)
import Language.Haskell.Liquid.ProofCombinators 

todo =  undefined


main :: IO ()
main = 
  do input     <- fromString <$> readFile "input.txt"
     let target = fromString "abcab"
     let mi1    = toMI    target input :: MI "abcab" SMTString
     let is1    = getIndex mi1 
     putStrLn ("Serial   Indices: " ++ show is1)
     let mi2    = toMIPar target input :: MI "abcab" SMTString
     let is2    = getIndex mi2 
     putStrLn ("Parallel Indices: " ++ show is2)
     putStrLn ("Are equal? " ++ show (is1 == is2))

test1 = indices target1 input1 
target1 = fromString "abcab"
input1  = fromString $ clone 100 "ababcabcab"


-- Interface 

indices :: SMTString -> SMTString -> Idxes Int 
indices target input 
  = case toMI target input :: MI "abcab" SMTString  of 
      MI _ i -> i 

mconcatPar :: forall (target :: Symbol). (KnownSymbol target) =>  Int -> [MI target SMTString] -> MI target SMTString
mconcatPar n xs = mconcat (mconcatPar' n xs)

{-@ Lazy mconcatPar' @-}
-- Termination proof is terribly slow and will change... 
{-@ mconcatPar' :: forall (target :: Symbol). (KnownSymbol target) =>  Int -> xs:[MI target SMTString] -> [MI target SMTString] @-}
mconcatPar' :: forall (target :: Symbol). (KnownSymbol target) =>  Int -> [MI target SMTString] -> [MI target SMTString]
mconcatPar' n xs | length xs <= n = [mconcat xs]  
mconcatPar' n xs = let (x, r) = splitAt n xs 
                   in mconcatPar' n (mconcat x:mconcatPar' n r)

toMIPar :: forall (target :: Symbol). (KnownSymbol target) =>   SMTString -> SMTString -> MI target SMTString 
toMIPar target input = mconcatPar n2 (toMI target <$> chunkString n1 input)
  where
    n1 = 2
    n2 = 2

toMI :: forall (target :: Symbol). (KnownSymbol target) =>   SMTString -> SMTString -> MI target SMTString 
toMI target input = if isNullString input then mempty else  MI input (makeIndexes' input target 0 (stringLen input - 1))

getIndex :: forall (target :: Symbol).  MI target SMTString -> Idxes Int 
getIndex (MI _ i) = i 

clone :: Int -> [a] -> [a]
clone i xs | i <= 0 = [] 
clone 1 xs = xs 
clone n xs = xs ++ clone (n-1) xs


-- Structure that defines valid indeces of a type level target 
-- symbol in a value level string

data MI (target :: Symbol) s where 
  MI ::               SMTString        -- input string
                   -> (Idxes Int)      -- valid indeces of target in input
                   -> MI target s
  deriving (Show)

{-@ data MI target s 
  = MI { input :: SMTString
       , idxes :: Idxes Int
       } @-}



{- data MI (target :: Symbol) s 
  = MI { input :: SMTString
       , idxes :: Idxes (GoodIndex input target)
       } @-}

{-@ type GoodIndex Input Target 
  = {i:Int |  IsGoodIndex Input Target i}
  @-}

{-@ predicate IsGoodIndex Input Target I
  =  (subString Input I (stringLen Target)  == Target)
  && (I + stringLen Target <= stringLen Input)
  && (0 <= I)
  @-}


mconcat :: forall (target :: Symbol). (KnownSymbol target) => [MI target SMTString] -> MI target SMTString
mconcat []       = mempty 
mconcat [x]      = x 
mconcat [x1, x2] = mappend x1 x2 
mconcat (x:xs)   = mappend x (mconcat xs)


{-@ reflect mempty @-}
mempty :: forall (target :: Symbol). MI target SMTString
mempty = MI stringEmp IdxEmp

{-@ reflect mappend @-}
mappend :: forall (target :: Symbol).  (KnownSymbol target) => MI target SMTString -> MI target SMTString -> MI target SMTString
mappend (MI i1 is1) (MI i2 is2)
  = MI (concatString i1 i2)  
       ((is1 `appendIdxes` makeIndexes i1 i2 (fromString (symbolVal (Proxy :: Proxy target))))
             `appendIdxes` mapIdxes (shift (stringLen i1)) is2)
            
 
mempty_left :: forall (target :: Symbol). (KnownSymbol target) => MI target SMTString -> Proof
{-@ mempty_left :: xs:MI target SMTString -> {mappend xs mempty == xs } @-}
mempty_left (MI i1 is1)
  =   mappend (MI i1 is1) (mempty :: MI target SMTString)
  ==. mappend (MI i1 is1) (MI stringEmp IdxEmp) 
  ==. MI (concatString i1 stringEmp)  
       (is1 `appendIdxes` mapIdxes (shift (stringLen i1)) IdxEmp
            `appendIdxes` makeIndexes i1 stringEmp (fromString (symbolVal (Proxy :: Proxy target))))
  ==. MI (concatString i1 stringEmp)  
       ((is1 `appendIdxes` IdxEmp)
            `appendIdxes` makeIndexes i1 stringEmp (fromString (symbolVal (Proxy :: Proxy target))))
  ==. MI (concatString i1 stringEmp)  
       (is1 `appendIdxes` makeIndexes i1 stringEmp (fromString (symbolVal (Proxy :: Proxy target))))
      ? appendIdxesEmp is1 
  ==. MI (concatString i1 stringEmp)  
       (is1 `appendIdxes` IdxEmp) 
      ? makeIndexesNullLeft i1 (fromString (symbolVal (Proxy :: Proxy target)))
  ==. MI (concatString i1 stringEmp) is1 
      ? appendIdxesEmp is1 
  ==. MI i1 is1 
      ? concatStringNeutral i1 
  *** QED 





mempty_right :: forall (target :: Symbol). (KnownSymbol target) => MI target SMTString -> Proof
{-@ mempty_right :: xs:MI target SMTString -> {mappend mempty xs == xs } @-}
mempty_right (MI i is)
  =   mappend (mempty :: MI target SMTString) (MI i is) 
  ==. mappend (MI stringEmp IdxEmp) (MI i is) 
  ==. MI (concatString stringEmp i)  
       (IdxEmp `appendIdxes` makeIndexes stringEmp i (fromString (symbolVal (Proxy :: Proxy target)))
               `appendIdxes` mapIdxes (shift (stringLen stringEmp)) is)
  ==. MI (concatString stringEmp i)  
       ( makeIndexes stringEmp i (fromString (symbolVal (Proxy :: Proxy target)))
        `appendIdxes`
         mapIdxes (shift (stringLen stringEmp)) is)
  ==. MI (concatString stringEmp i)  
       ( makeIndexes stringEmp i (fromString (symbolVal (Proxy :: Proxy target)))
         `appendIdxes` 
         mapIdxes (shift 0) is)
  ==. MI (concatString stringEmp i)  
       (makeIndexes stringEmp i (fromString (symbolVal (Proxy :: Proxy target)))
        `appendIdxes` 
        is)
       ? mapShiftZero is 
  ==. MI (concatString stringEmp i)  
       (IdxEmp `appendIdxes` is) 
      ? makeIndexesNullRight i (fromString (symbolVal (Proxy :: Proxy target)))
  ==. MI (concatString stringEmp i) is 
  ==. MI i is 
      ? concatStringNeutralRight i
  *** QED 

{-@ mappend_assoc 
  :: x:MI target SMTString -> y:MI target SMTString -> z:MI target SMTString
  -> {mappend x (mappend y z) = mappend (mappend x y) z}
  @-}
mappend_assoc 
     :: forall (target :: Symbol). (KnownSymbol target) 
     => MI target SMTString ->  MI target SMTString ->  MI target SMTString -> Proof
mappend_assoc x@(MI xi xis) y@(MI yi yis) z@(MI zi zis)
  | stringLen (fromString (symbolVal (Proxy :: Proxy target))) <= stringLen yi 
  =   mappend x (mappend y z)
  ==. mappend (MI xi xis) (mappend (MI yi yis) (MI zi zis))
  ==. mappend (MI xi xis) 
              (MI (concatString yi zi)  
                  ((yis 
                    `appendIdxes` makeIndexes yi zi (fromString (symbolVal (Proxy :: Proxy target))))
                    `appendIdxes` mapIdxes (shift (stringLen yi)) zis))
  ==. MI (concatString xi (concatString yi zi))  
         ((xis `appendIdxes` 
               makeIndexes xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target))))
               `appendIdxes` 
                  mapIdxes (shift (stringLen xi)) 
                  ((yis 
                    `appendIdxes` makeIndexes yi zi (fromString (symbolVal (Proxy :: Proxy target))))
                    `appendIdxes` mapIdxes (shift (stringLen yi)) zis)
              )
  ==. MI (concatString (concatString xi yi) zi)  
         ((xis `appendIdxes` 
               makeIndexes xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target))))
               `appendIdxes` 
                  mapIdxes (shift (stringLen xi)) 
                  ((yis 
                    `appendIdxes` makeIndexes yi zi (fromString (symbolVal (Proxy :: Proxy target))))
                    `appendIdxes` mapIdxes (shift (stringLen yi)) zis)
              )
      ? concatStringAssoc xi yi zi 
  ==. MI (concatString (concatString xi yi) zi)  
         ((xis `appendIdxes` 
               makeIndexes xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target))))
               `appendIdxes` 
                  (
                    (mapIdxes (shift (stringLen xi)) (yis 
                    `appendIdxes` makeIndexes yi zi (fromString (symbolVal (Proxy :: Proxy target)))))
                    `appendIdxes` 
                    mapIdxes (shift (stringLen xi)) (mapIdxes (shift (stringLen yi)) zis))
              )
      ? map_append (shift (stringLen xi)) 
                   (yis `appendIdxes` makeIndexes yi zi (fromString (symbolVal (Proxy :: Proxy target)))) 
                   (mapIdxes (shift (stringLen yi)) zis)
  ==. MI (concatString (concatString xi yi) zi)  
         ((xis `appendIdxes` 
               makeIndexes xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target))))
               `appendIdxes` 
                  (
                    (mapIdxes (shift (stringLen xi)) yis 
                    `appendIdxes` (mapIdxes (shift (stringLen xi)) (makeIndexes yi zi (fromString (symbolVal (Proxy :: Proxy target))))))
                    `appendIdxes` 
                    mapIdxes (shift (stringLen xi)) (mapIdxes (shift (stringLen yi)) zis))
              )
      ? map_append (shift (stringLen xi)) yis (makeIndexes yi zi (fromString (symbolVal (Proxy :: Proxy target))))
  ==. MI (concatString (concatString xi yi) zi)  
         ((xis `appendIdxes` 
               makeIndexes xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target))))
               `appendIdxes` 
                  (
                    (mapIdxes (shift (stringLen xi)) yis 
                    `appendIdxes` (mapIdxes (shift (stringLen xi)) (makeIndexes yi zi (fromString (symbolVal (Proxy :: Proxy target))))))
                    `appendIdxes` 
                    mapIdxes (shift (stringLen (concatString xi yi))) zis)
              )
      ? map_len_fusion xi yi zis 
-- ((x1~x2) ~ ((x3~x4) ~ x5))
-- == 
--   ((((x1~x2) ~x3) ~x4) ~x5
  ==. MI (concatString (concatString xi yi) zi)
         (((( xis 
               `appendIdxes` 
              makeIndexes xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target))))                      `appendIdxes` mapIdxes (shift (stringLen xi)) yis)
               `appendIdxes` 
              mapIdxes (shift (stringLen xi)) yis)
               `appendIdxes`
              mapIdxes (shift (stringLen (concatString xi yi))) zis)

      ? appendReorder xis
                      (makeIndexes xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target))))
                      (mapIdxes (shift (stringLen xi)) yis)
                      (mapIdxes (shift (stringLen xi)) (makeIndexes yi zi (fromString (symbolVal (Proxy :: Proxy target)))))
                      (mapIdxes (shift (stringLen (concatString xi yi))) zis)
-- ((((x1 ~ x2) ~ x3) ~ x4) ~ x5)
-- 
-- ((((x1 ~ x2) ~ x3) ~ x4) ~ x5)

  ==. MI (concatString (concatString xi yi) zi)
         (((( xis 
               `appendIdxes` 
              makeIndexes xi yi (fromString (symbolVal (Proxy :: Proxy target))))
               `appendIdxes` 
              mapIdxes (shift (stringLen xi)) yis)
               `appendIdxes`
              makeIndexes (concatString xi yi) zi (fromString (symbolVal (Proxy :: Proxy target))))
               `appendIdxes` 
              mapIdxes (shift (stringLen (concatString xi yi))) zis 
          )
      ? shiftIndexes xi yi zi (fromString (symbolVal (Proxy :: Proxy target)))
  ==. mappend (MI (concatString xi yi)  
                  ( (xis `appendIdxes` makeIndexes xi yi (fromString (symbolVal (Proxy :: Proxy target))))
                       `appendIdxes` mapIdxes (shift (stringLen xi)) yis
                  )
              ) (MI zi zis)
  ==. mappend (mappend (MI xi xis) (MI yi yis)) (MI zi zis)
  *** QED 



mappend_assoc x@(MI xi xis) y@(MI yi yis) z@(MI zi zis)
  | stringLen yi < stringLen (fromString (symbolVal (Proxy :: Proxy target))) 
  =   mappend x (mappend y z)
  ==. mappend (MI xi xis) (mappend (MI yi yis) (MI zi zis))
  ==. mappend (MI xi xis) 
              (MI (concatString yi zi)  
                  ((yis 
                    `appendIdxes` makeIndexes yi zi (fromString (symbolVal (Proxy :: Proxy target))))
                    `appendIdxes` mapIdxes (shift (stringLen yi)) zis))
  ==. MI (concatString xi (concatString yi zi))  
         ((xis `appendIdxes` 
               makeIndexes xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target))))
               `appendIdxes` 
                  mapIdxes (shift (stringLen xi)) 
                  ((yis 
                    `appendIdxes` makeIndexes yi zi (fromString (symbolVal (Proxy :: Proxy target))))
                    `appendIdxes` mapIdxes (shift (stringLen yi)) zis)
              )
  ==. MI (concatString (concatString xi yi) zi)  
         ((xis `appendIdxes` 
               makeIndexes xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target))))
               `appendIdxes` 
                  mapIdxes (shift (stringLen xi)) 
                  ((yis 
                    `appendIdxes` makeIndexes yi zi (fromString (symbolVal (Proxy :: Proxy target))))
                    `appendIdxes` mapIdxes (shift (stringLen yi)) zis)
              )
      ? concatStringAssoc xi yi zi 
  ==. MI (concatString (concatString xi yi) zi)  
         ((xis `appendIdxes` 
               makeIndexes xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target))))
               `appendIdxes` 
                  mapIdxes (shift (stringLen xi)) 
                  ((IdxEmp 
                    `appendIdxes` makeIndexes yi zi (fromString (symbolVal (Proxy :: Proxy target))))
                    `appendIdxes` mapIdxes (shift (stringLen yi)) zis)
              )
        ? emptyIndexes y yis
  ==. MI (concatString (concatString xi yi) zi)  
         ((xis `appendIdxes` 
               makeIndexes xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target))))
               `appendIdxes` 
                  mapIdxes (shift (stringLen xi)) 
                  (makeIndexes yi zi (fromString (symbolVal (Proxy :: Proxy target)))
                    `appendIdxes` mapIdxes (shift (stringLen yi)) zis)
              )
  ==. MI (concatString (concatString xi yi) zi)  
         ((xis `appendIdxes` 
               makeIndexes xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target))))
               `appendIdxes` 
                  (mapIdxes (shift (stringLen xi)) (makeIndexes yi zi (fromString (symbolVal (Proxy :: Proxy target))))
                  `appendIdxes` mapIdxes (shift (stringLen xi)) (mapIdxes (shift (stringLen yi)) zis))
              )
      ? map_append (shift (stringLen xi)) 
                   (makeIndexes yi zi (fromString (symbolVal (Proxy :: Proxy target)))) 
                   (mapIdxes (shift (stringLen yi)) zis)

  ==. MI (concatString (concatString xi yi) zi)  
         ((xis `appendIdxes` 
               makeIndexes xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target))))
               `appendIdxes` 
                  (mapIdxes (shift (stringLen xi)) (makeIndexes yi zi (fromString (symbolVal (Proxy :: Proxy target))))
                  `appendIdxes` mapIdxes (shift (stringLen xi)) (mapIdxes (shift (stringLen yi)) zis))
              )
      ? map_len_fusion xi yi zis 
-- ((x1~x2) ~ (x3~x4))
-- == 
-- (x1 ~ (x2~x3)) ~ x4
  ==. MI (concatString (concatString xi yi) zi)  
         ((xis `appendIdxes` 
               (makeIndexes xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target)))
               `appendIdxes` 
                mapIdxes (shift (stringLen xi)) (makeIndexes yi zi (fromString (symbolVal (Proxy :: Proxy target)))))
                  `appendIdxes` mapIdxes (shift (stringLen xi)) (mapIdxes (shift (stringLen yi)) zis))
              )
      ? appendGroupNew xis
                       (makeIndexes xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target))))
                       (mapIdxes (shift (stringLen xi)) (makeIndexes yi zi (fromString (symbolVal (Proxy :: Proxy target)))))
                       (mapIdxes (shift (stringLen xi)) (mapIdxes (shift (stringLen yi)) zis))


  ==. MI (concatString (concatString xi yi) zi)  
         ((xis `appendIdxes` 
               (makeIndexes xi yi (fromString (symbolVal (Proxy :: Proxy target)))
               `appendIdxes` 
                makeIndexes (concatString xi yi) zi (fromString (symbolVal (Proxy :: Proxy target))))
                  `appendIdxes` mapIdxes (shift (stringLen xi)) (mapIdxes (shift (stringLen yi)) zis))
              )
      ? shiftNewIndexes xi yi zi (fromString (symbolVal (Proxy :: Proxy target)))
  ==. MI (concatString (concatString xi yi) zi)  
         ((xis `appendIdxes` 
               (makeIndexes xi yi (fromString (symbolVal (Proxy :: Proxy target)))
               `appendIdxes` 
                makeIndexes (concatString xi yi) zi (fromString (symbolVal (Proxy :: Proxy target))))
                  `appendIdxes` mapIdxes (shift (stringLen (concatString xi yi))) zis)
              )
      ? map_len_fusion xi yi zis 

-- (x1 ~ (x2 ~ x3)) ~ x4 == ((x1 ~ x2) ~ x3) ~ x4
  ==. MI (concatString (concatString xi yi) zi)  
         (((xis `appendIdxes` makeIndexes xi yi (fromString (symbolVal (Proxy :: Proxy target))))
         `appendIdxes`
            (makeIndexes (concatString xi yi) zi (fromString (symbolVal (Proxy :: Proxy target)))))
         `appendIdxes` 
            mapIdxes (shift (stringLen (concatString xi yi))) zis )
      ? appendUnGroupNew xis 
                         (makeIndexes xi yi (fromString (symbolVal (Proxy :: Proxy target))))
                         (makeIndexes (concatString xi yi) zi (fromString (symbolVal (Proxy :: Proxy target))))
                         (mapIdxes (shift (stringLen (concatString xi yi))) zis)

  ==. MI (concatString (concatString xi yi) zi)  
        ((((xis `appendIdxes` makeIndexes xi yi (fromString (symbolVal (Proxy :: Proxy target))))
                       `appendIdxes` IdxEmp
                  )
         `appendIdxes`
            (makeIndexes (concatString xi yi) zi (fromString (symbolVal (Proxy :: Proxy target)))))
         `appendIdxes` 
            mapIdxes (shift (stringLen (concatString xi yi))) zis )
          ? appendIdxesEmp (xis `appendIdxes` makeIndexes xi yi (fromString (symbolVal (Proxy :: Proxy target))))
  ==. MI (concatString (concatString xi yi) zi)  
        ((((xis `appendIdxes` makeIndexes xi yi (fromString (symbolVal (Proxy :: Proxy target))))
                       `appendIdxes` mapIdxes (shift (stringLen xi)) IdxEmp
                  )
         `appendIdxes`
            (makeIndexes (concatString xi yi) zi (fromString (symbolVal (Proxy :: Proxy target)))))
         `appendIdxes` 
            mapIdxes (shift (stringLen (concatString xi yi))) zis )
  ==. MI (concatString (concatString xi yi) zi)  
        ((((xis `appendIdxes` makeIndexes xi yi (fromString (symbolVal (Proxy :: Proxy target))))
                       `appendIdxes` mapIdxes (shift (stringLen xi)) yis
                  )
         `appendIdxes`
            (makeIndexes (concatString xi yi) zi (fromString (symbolVal (Proxy :: Proxy target)))))
         `appendIdxes` 
            mapIdxes (shift (stringLen (concatString xi yi))) zis )
      ?emptyIndexes y yis
  ==. mappend (MI (concatString xi yi)  
                  ( (xis `appendIdxes` makeIndexes xi yi (fromString (symbolVal (Proxy :: Proxy target))))
                       `appendIdxes` mapIdxes (shift (stringLen xi)) yis
                  )
              ) (MI zi zis)
  ==. mappend (mappend (MI xi xis) (MI yi yis)) (MI zi zis)
  *** QED 





emptyIndexes :: forall (target :: Symbol). (KnownSymbol target) => MI target SMTString -> Idxes Int -> Proof
{-@ emptyIndexes :: MI target SMTString -> is:Idxes Int -> { is == IdxEmp } @-}
{- emptyIndexes :: MI target {i:SMTString | stringLen i < stringLen target } -> is:{Idxes Int | is == indexes mi } -> { is == IdxEmp } @-}
emptyIndexes = todo 



{-@ shiftIndexes
  :: xi:SMTString 
  -> yi:SMTString 
  -> zi:SMTString 
  -> tg:{SMTString | stringLen tg <= stringLen yi } 
  -> {  (makeIndexes xi (concatString yi zi) tg == makeIndexes xi yi tg)  
        && 
        (mapIdxes (shift (stringLen xi)) (makeIndexes yi zi tg) == makeIndexes (concatString xi yi) zi tg)
     }
  @-}
shiftIndexes :: SMTString -> SMTString -> SMTString -> SMTString -> Proof
shiftIndexes xi yi zi tg = shiftIndexesLeft xi yi zi tg &&& shiftIndexesRight xi yi zi tg 



{-@ shiftIndexesLeft
  :: xi:SMTString 
  -> yi:SMTString 
  -> zi:SMTString 
  -> tg:{SMTString | stringLen tg <= stringLen yi } 
  -> {  makeIndexes xi (concatString yi zi) tg == makeIndexes xi yi tg}
  @-}
shiftIndexesLeft :: SMTString -> SMTString -> SMTString -> SMTString -> Proof
shiftIndexesLeft xi yi zi tg
  | stringLen tg < 2 
  =   makeIndexes xi (concatString yi zi) tg 
  ==. IdxEmp
  ==. makeIndexes xi yi tg 
  *** QED 
  | otherwise
  =   makeIndexes xi (concatString yi zi) tg 
  ==. makeIndexes' (concatString xi (concatString yi zi)) tg 
                   (maxInt (stringLen xi - (stringLen tg-1)) (-1))
                   (stringLen xi - 1)
  ==. makeIndexes' (concatString (concatString xi yi) zi) tg 
                   (maxInt (stringLen xi - (stringLen tg-1)) (-1))
                   (stringLen xi - 1)
     ?concatStringAssoc xi yi zi 
  -- HERE HERE HERE 
  ==. makeIndexes' (concatString xi yi) tg 
                   (maxInt (stringLen xi - (stringLen tg-1)) (-1))
                   (stringLen xi - 1)                
      ? concatMakeIndexes (maxInt (stringLen xi - (stringLen tg-1)) (-1)) (stringLen xi - 1) tg (concatString xi yi) zi 
  ==. makeIndexes xi yi tg 
  *** QED 



{-@ concatMakeIndexes
  :: lo:{Int | -1 <= lo} -> hi:{Int | lo <= hi}
  -> target: SMTString
  -> input : {SMTString | hi + stringLen target <= stringLen input } 
  -> input': SMTString   
  -> {  makeIndexes' (concatString input input') target lo hi == makeIndexes' input target lo hi }
  / [hi - lo]  @-}
concatMakeIndexes :: Int -> Int -> SMTString -> SMTString -> SMTString  -> Proof
concatMakeIndexes lo hi target input input' 
  | lo == hi, isGoodIndex input target lo
  =   makeIndexes' input target lo hi
  ==. lo `Idxs` IdxEmp
  ==. makeIndexes' (concatString input input') target lo hi 
      ? isGoodIndexConcatString input input' target lo  
  *** QED 
  | lo == hi
  =  makeIndexes' input target lo hi 
  ==. IdxEmp
  ==. makeIndexes' (concatString input input') target lo hi
      ? isGoodIndexConcatString input input' target lo  
  *** QED 
concatMakeIndexes lo hi target input input' 
  | isGoodIndex input target lo
  =   makeIndexes' input target lo hi
  ==. lo `Idxs` (makeIndexes' input target (lo + 1) hi)
  ==. lo `Idxs` (makeIndexes' (concatString input input') target (lo + 1) hi)
       ? concatMakeIndexes (lo+1) hi target input input'
  ==. makeIndexes'  (concatString input input') target lo hi
      ? isGoodIndexConcatString input input' target lo  
  *** QED 
  | otherwise 
  =   makeIndexes' input target lo hi
  ==. makeIndexes' input target (lo + 1) hi
  ==. makeIndexes' (concatString input input') target (lo + 1) hi
       ? concatMakeIndexes (lo+1) hi target input input'
  ==. makeIndexes'  (concatString input input') target lo hi
      ? isGoodIndexConcatString input input' target lo  
  *** QED 



{-@ isGoodIndexConcatString 
  :: input:SMTString -> input':SMTString -> tg:SMTString -> i:{Int | i + stringLen tg <= stringLen input }
  -> {((isGoodIndex input tg i) <=> isGoodIndex (concatString input input') tg i)
     } @-}
isGoodIndexConcatString :: SMTString -> SMTString -> SMTString -> Int -> Proof 
isGoodIndexConcatString input input' tg i 
  =   isGoodIndex input tg i 
  ==. (subString input i (stringLen tg)  == tg  
      && i + stringLen tg <= stringLen input
      && 0 <= i) 
  ==. (subString (concatString input input') i (stringLen tg)  == tg  
      && i + stringLen tg <= stringLen input 
      && 0 <= i)   
      ? (subStringConcat input input' (stringLen tg) i *** QED )
  ==. (subString (concatString input input') i (stringLen tg)  == tg  
      && i + stringLen tg <= stringLen (concatString input input') 
      && 0 <= i)   
      ? (((stringLen input <= stringLen (concatString input input') *** QED ) &&& (lenConcat input input') *** QED))
  ==. isGoodIndex (concatString input input') tg i 
  *** QED 






{-@ shiftIndexesRight
  :: xi:SMTString 
  -> yi:SMTString 
  -> zi:SMTString 
  -> tg:{SMTString | stringLen tg <= stringLen yi } 
  -> { mapIdxes (shift (stringLen xi)) (makeIndexes yi zi tg) == makeIndexes (concatString xi yi) zi tg }
  @-}
shiftIndexesRight :: SMTString -> SMTString -> SMTString -> SMTString -> Proof
shiftIndexesRight = todo 



{-@ shiftNewIndexes
  :: xi:SMTString 
  -> yi:SMTString 
  -> zi:SMTString 
  -> tg:{SMTString | stringLen yi < stringLen tg  } 
  -> {  appendIdxes (makeIndexes xi (concatString yi zi) tg) (mapIdxes (shift (stringLen xi)) (makeIndexes yi zi tg)) == appendIdxes (makeIndexes xi yi tg) (makeIndexes (concatString xi yi) zi tg)
     }
  @-}
shiftNewIndexes :: SMTString -> SMTString -> SMTString -> SMTString -> Proof
shiftNewIndexes = todo 


map_len_fusion :: SMTString -> SMTString -> Idxes Int -> Proof
{-@ map_len_fusion 
  :: xi:SMTString 
  -> yi:SMTString 
  -> zis:Idxes Int 
  -> {  mapIdxes (shift (stringLen (concatString xi yi))) zis == mapIdxes (shift (stringLen xi)) (mapIdxes (shift (stringLen yi)) zis) 
     }
  @-}
map_len_fusion xi yi IdxEmp 
  =   mapIdxes (shift (stringLen (concatString xi yi))) IdxEmp
  ==. IdxEmp
  ==. mapIdxes (shift (stringLen xi)) IdxEmp
  ==. mapIdxes (shift (stringLen xi)) (mapIdxes (shift (stringLen yi)) IdxEmp)
  *** QED  
map_len_fusion xi yi (Idxs i is)
  =   mapIdxes (shift (stringLen (concatString xi yi))) (Idxs i is)
  ==. shift (stringLen (concatString xi yi)) i `Idxs` mapIdxes (shift (stringLen (concatString xi yi))) is 
  ==. shift (stringLen xi + stringLen yi) i `Idxs` mapIdxes (shift (stringLen (concatString xi yi))) is 
      ? concatLen xi yi 
  ==. shift (stringLen xi) (shift (stringLen yi) i) `Idxs` mapIdxes (shift (stringLen (concatString xi yi))) is 
      ? concatLen xi yi 
  ==. shift (stringLen xi) (shift (stringLen yi) i) `Idxs` mapIdxes (shift (stringLen xi)) (mapIdxes (shift (stringLen yi)) is)
      ? map_len_fusion xi yi is 
  ==. mapIdxes (shift (stringLen xi)) (shift (stringLen yi) i `Idxs` mapIdxes (shift (stringLen yi)) is)
  ==. mapIdxes (shift (stringLen xi)) (mapIdxes (shift (stringLen yi)) (i `Idxs` is))
  *** QED 


-- (x1 ~ x2) ~ (x3 ~ x4)
-- == 
-- ((x1 ~ (x2 ~ x3)) ~ x4)


appendGroupNew :: Idxes a -> Idxes a -> Idxes a -> Idxes a -> Proof
{-@ appendGroupNew 
  :: x1:Idxes a 
  -> x2:Idxes a 
  -> x3:Idxes a 
  -> x4:Idxes a 
  -> {   (appendIdxes (appendIdxes x1 x2) (appendIdxes x3 x4))
      == (appendIdxes (appendIdxes x1 (appendIdxes x2 x3)) x4)
     } @-}
appendGroupNew = todo



-- (x1 ~ (x2 ~ x3)) ~ x4 == ((x1 ~ x2) ~ x3) ~ x4

appendUnGroupNew :: Idxes a -> Idxes a -> Idxes a -> Idxes a -> Proof
{-@ appendUnGroupNew 
  :: x1:Idxes a 
  -> x2:Idxes a 
  -> x3:Idxes a 
  -> x4:Idxes a 
  -> {   ((appendIdxes (appendIdxes (appendIdxes x1 x2) x3) x4))
      == (appendIdxes (appendIdxes x1 (appendIdxes x2 x3)) x4)
     } @-}
appendUnGroupNew = todo


appendReorder :: Idxes a -> Idxes a -> Idxes a -> Idxes a -> Idxes a -> Proof
{-@ appendReorder 
  :: x1:Idxes a 
  -> x2:Idxes a 
  -> x3:Idxes a 
  -> x4:Idxes a 
  -> x5:Idxes a 
  -> {   (appendIdxes (appendIdxes x1 x2) (appendIdxes (appendIdxes x3 x4) x5))
      == (appendIdxes (appendIdxes (appendIdxes (appendIdxes x1 x2) x3) x4) x5)
     } @-}
appendReorder = todo


-- ((x1~x2) ~ ((x3~x4) ~ x5))
-- == 
--   ((((x1~x2) ~x3) ~x4) ~x5

map_append :: (a -> b) -> Idxes a -> Idxes a -> Proof
{-@ map_append 
     :: f:(a -> b) -> xs:Idxes a -> ys:Idxes a 
     -> {mapIdxes f (appendIdxes xs ys) == appendIdxes (mapIdxes f xs) (mapIdxes f ys)}
  @-}
map_append = todo 

mapShiftZero :: Idxes Int -> Proof
{-@ mapShiftZero :: is:Idxes Int -> {mapIdxes (shift 0) is == is } @-}
mapShiftZero IdxEmp 
  = mapIdxes (shift 0) IdxEmp ==. IdxEmp *** QED
mapShiftZero (Idxs i is)
  =   mapIdxes (shift 0) (Idxs i is)
  ==. shift 0 i `Idxs` mapIdxes (shift 0) is 
  ==. i `Idxs` is ? mapShiftZero is  
  *** QED 

-- String Library 

concatLen :: SMTString -> SMTString -> Proof
{-@ assume concatLen :: x:SMTString -> y:SMTString -> { stringLen (concatString x y) == stringLen x + stringLen y } @-}
concatLen = undefined

concatStringNeutral :: SMTString -> Proof
{-@ concatStringNeutral :: x:SMTString -> {concatString x stringEmp == x} @-}
concatStringNeutral = undefined

concatStringNeutralRight :: SMTString -> Proof
{-@ concatStringNeutralRight :: x:SMTString -> {concatString stringEmp x == x} @-}
concatStringNeutralRight = undefined

concatStringAssoc :: SMTString -> SMTString -> SMTString -> Proof
{-@ concatStringAssoc 
  :: x:SMTString -> y:SMTString -> z:SMTString 
  -> {concatString (concatString x y) z == concatString x (concatString y z) } @-}
concatStringAssoc = undefined


-------------------------------------------------------------------------------
----------  Indexing ----------------------------------------------------------
-------------------------------------------------------------------------------

   
data Idxes a = IdxEmp | Idxs a (Idxes a) deriving (Show, Eq)
{-@ data Idxes [idxlen] a = IdxEmp | Idxs {idxhd :: a , idxtl :: Idxes a} @-}


{-@ measure idxlen @-}
{-@ idxlen :: Idxes a -> Nat @-} 
idxlen :: Idxes a -> Int 
idxlen IdxEmp = 0 
idxlen (Idxs _ xs) = 1 + idxlen xs 

{-@ reflect mapIdxes @-}
mapIdxes :: (a -> b) -> Idxes a -> Idxes b
mapIdxes _ IdxEmp = IdxEmp
mapIdxes f (Idxs x xs) = Idxs (f x) (mapIdxes f xs)

{-@ reflect appendIdxes @-}
appendIdxes :: Idxes a -> Idxes a -> Idxes a 
appendIdxes IdxEmp xs = xs 
appendIdxes (Idxs x xs) ys = Idxs x (appendIdxes xs ys)

{-@ reflect shift @-}
shift :: Int -> Int -> Int 
shift x y = x + y 

{-@ symbolVal :: forall n proxy. KnownSymbol n => x:proxy n 
  -> {v:String | v == n && v == symbolVal x } @-}
{-@ measure symbolVal :: p n -> String @-}

{-@ reflect makeIndexes @-}
makeIndexes :: SMTString -> SMTString -> SMTString -> Idxes Int 
makeIndexes s1 s2 target
  | stringLen target < 2 
  = IdxEmp
  | otherwise
  = makeIndexes' (concatString s1 s2) target
                 (maxInt (stringLen s1 - (stringLen target-1)) (-1))
                 (stringLen s1 - 1)


{-@ reflect maxInt @-}
maxInt :: Int -> Int -> Int 
maxInt x y = if x <= y then y else x 

{-@ reflect makeIndexes' @-}

makeIndexes' :: SMTString -> SMTString -> Int -> Int -> Idxes Int 
{-@ makeIndexes' :: input:SMTString -> target:SMTString -> lo:{Int | -1 <= lo} -> hi:{Int | lo <= hi} -> Idxes (GoodIndex input target) / [hi - lo] @-}
makeIndexes' input target lo hi 
  | lo == hi, isGoodIndex input target lo
  = lo `Idxs` IdxEmp
  | lo == hi 
  = IdxEmp
makeIndexes' input target lo hi 
  | isGoodIndex input target lo
  = lo `Idxs` (makeIndexes' input target (lo + 1) hi)
  | otherwise 
  =    makeIndexes' input target (lo + 1) hi 

{-@ reflect isGoodIndex @-}
isGoodIndex :: SMTString -> SMTString -> Int -> Bool 
{-@ isGoodIndex :: input:SMTString -> target:SMTString -> i:Int 
  -> {b:Bool | Prop b <=> IsGoodIndex input target i} @-}
isGoodIndex input target i 
  =  subString input i (stringLen target)  == target  
  && i + stringLen target <= stringLen input
  && 0 <= i    
-------------------------------------------------------------------------------
----------  Indexing Properties -----------------------------------------------
-------------------------------------------------------------------------------

{-@ appendIdxesEmp :: xs:Idxes a -> {appendIdxes xs IdxEmp = xs } @-} 
appendIdxesEmp :: Idxes a -> Proof 
appendIdxesEmp IdxEmp 
  =   appendIdxes IdxEmp IdxEmp
  ==. IdxEmp
  *** QED 
appendIdxesEmp (Idxs x xs) 
  =   appendIdxes (Idxs x xs) IdxEmp
  ==. Idxs x (appendIdxes xs IdxEmp)
  ==. Idxs x xs ? appendIdxesEmp xs 
  *** QED 


makeIndexesNullRight :: SMTString -> SMTString -> Proof 
{-@ makeIndexesNullRight 
  :: s1:SMTString 
  -> t:SMTString 
  -> {makeIndexes stringEmp s1 t == IdxEmp } @-} 
makeIndexesNullRight s t 
  | stringLen t < 2 
  = makeIndexes stringEmp s t  ==. IdxEmp *** QED 
makeIndexesNullRight s t 
  =   makeIndexes stringEmp s t
  ==. makeIndexes' (concatString stringEmp s) t
                   (maxInt (1 + stringLen stringEmp - stringLen t) (-1))
                   (stringLen stringEmp - 1)
  ==. makeIndexes' s t
                   (maxInt (1 - stringLen t) (-1))
                   (-1)
      ? concatStringNeutralRight s 
  ==. makeIndexes' s t (-1) (-1)
  ==. IdxEmp ? makeIndexesNullRightEmp s t  
  *** QED 


{-@ makeIndexesNullRightEmp :: s:SMTString -> t:SMTString -> {makeIndexes' s t (-1) (-1) == IdxEmp } @-}
makeIndexesNullRightEmp :: SMTString -> SMTString -> Proof
makeIndexesNullRightEmp s t 
  | not (isGoodIndex s t (-1))
  =   makeIndexes' s t (-1) (-1) 
  ==. IdxEmp
  *** QED 

makeIndexesNullLeft :: SMTString -> SMTString -> Proof 
{-@ makeIndexesNullLeft 
  :: s:SMTString 
  -> t:SMTString 
  -> {makeIndexes s stringEmp t == IdxEmp } @-} 
makeIndexesNullLeft s t 
  | stringLen t < 2 
  = makeIndexes s stringEmp t ==. IdxEmp *** QED 
makeIndexesNullLeft  s t 
  | 2 + stringLen s <= stringLen t
  =   makeIndexes s stringEmp t
  ==. makeIndexes' (concatString s stringEmp) t
                   (maxInt (1 + stringLen s - stringLen t)  (-1))
                   (stringLen s - 1)
  ==. makeIndexes' s t
                   (-1)
                   (stringLen s - 1) 
                   ? concatStringNeutral s
  ==. makeIndexes' s t
                   (-1)
                   (stringLen s - 1)
  ==. IdxEmp ? makeIndexesNull1 s t (-1) (stringLen s - 1)
  *** QED 
makeIndexesNullLeft s t 
  =   makeIndexes s stringEmp t
  ==. makeIndexes' (concatString s stringEmp) t
                   (maxInt (1 + stringLen s - stringLen t)  (-1))
                   (stringLen s - 1)
  ==. makeIndexes' (concatString s stringEmp) t
                   (1 + stringLen s - stringLen t)
                   (stringLen s - 1)
  ==. makeIndexes' s t
                   (1 + stringLen s - stringLen t)
                   (stringLen s - 1) ? concatStringNeutral s 
  ==. IdxEmp ? makeIndexesNull2 s t (1 + stringLen s - stringLen t) (stringLen s - 1)
  *** QED 


makeIndexesNull1 :: SMTString -> SMTString -> Int -> Int -> Proof 
{-@ makeIndexesNull1 
  :: s:SMTString 
  -> t:{SMTString |  2 + stringLen s <= stringLen t } 
  -> lo:{Int | -1 <= lo } 
  -> hi:{Int | lo <= hi}
  -> {makeIndexes' s t lo hi == IdxEmp } / [hi - lo] @-} 
makeIndexesNull1 s1 t lo hi
  | lo == hi, not (isGoodIndex s1 t lo)
  = makeIndexes' s1 t lo hi ==. IdxEmp *** QED  
  | not (isGoodIndex s1 t lo)
  =   makeIndexes' s1 t lo hi
  ==. makeIndexes' s1 t (lo + 1) hi 
  ==. IdxEmp ? makeIndexesNull1 s1 t (lo+1) hi
  *** QED 


makeIndexesNull2 :: SMTString -> SMTString -> Int -> Int -> Proof 
{-@ makeIndexesNull2 
  :: s:SMTString 
  -> t:{SMTString | stringLen t < 2 + stringLen s } 
  -> lo:{Int | -1 <= lo && 1 + stringLen s - stringLen t <= lo  } 
  -> hi:{Int | lo <= hi}
  -> {makeIndexes' s t lo hi == IdxEmp } / [hi - lo] @-} 
makeIndexesNull2 s1 t lo hi
  | lo == hi, not (isGoodIndex s1 t lo)
  = makeIndexes' s1 t lo hi ==. IdxEmp *** QED  
  | not (isGoodIndex s1 t lo)
  =   makeIndexes' s1 t lo hi
  ==. makeIndexes' s1 t (lo + 1) hi 
  ==. IdxEmp ? makeIndexesNull2 s1 t (lo+1) hi
  *** QED 
 
