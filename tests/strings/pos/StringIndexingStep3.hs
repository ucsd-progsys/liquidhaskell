{-
NV TODO 
1. refine data type
2. connect it with Steps 1 & 2
3. connect it with dyn programming 
-}



{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs               #-}


{-@ LIQUID "--higherorder"         @-}
{-@ LIQUID "--totality"            @-}
{-@ LIQUID "--exactdc"             @-}

module Main where

import Language.Haskell.Liquid.String
import GHC.TypeLits
import Data.String hiding (fromString)
import Data.Proxy 
import Prelude hiding (mempty, mappend, id, mconcat, map)
import Language.Haskell.Liquid.ProofCombinators 

import Data.Maybe 

-- | Interface 

main :: IO ()
main = 
   do input     <- fromString <$> readFile "input.txt"
      let mi1    = toMI input :: MI "abcab" SMTString
      let is1    = getIndex mi1 
      putStrLn ("Serial   Indices: " ++ show is1)
      let mi2    = toMIPar input :: MI "abcab" SMTString
      let is2    = getIndex mi2 
      putStrLn ("Parallel Indices: " ++ show is2)
      putStrLn ("Are equal? " ++ show (is1 == is2))

{-
main :: IO ()
main = 
  do input     <- fromString <$> readFile "input.txt"
     case someSymbolVal "x" of 
            SomeSymbol (_ :: Proxy y) ->            
      let mi1    = toMI input :: MI y SMTString
      let is1    = getIndex mi1 
      putStrLn ("Serial   Indices: " ++ show is1)
      let mi2    = toMIPar input :: MI "abcab" SMTString
      let is2    = getIndex mi2 
      putStrLn ("Parallel Indices: " ++ show is2)
      putStrLn ("Are equal? " ++ show (is1 == is2))


-}

test1   = indices input1 
input1  = fromString $ clone 100 "ababcabcab"


indices :: SMTString -> List Int 
indices input 
  = case toMI input :: MI "abcab" SMTString  of 
      MI _ i -> i 


{-



  |
-}

mconcatPar :: forall (target :: Symbol). (KnownSymbol target) =>  Int -> [MI target SMTString] -> MI target SMTString
mconcatPar n xs = mconcat (mconcatPar' n xs)

{-@ Lazy mconcatPar' @-}
-- Termination proof is terribly slow and will change... 
{-@ mconcatPar' :: forall (target :: Symbol). (KnownSymbol target) =>  Int -> xs:[MI target SMTString] -> [MI target SMTString] @-}
mconcatPar' :: forall (target :: Symbol). (KnownSymbol target) =>  Int -> [MI target SMTString] -> [MI target SMTString]
mconcatPar' n xs | length xs <= n = [mconcat xs]  
mconcatPar' n xs = let (x, r) = splitAt n xs 
                   in mconcatPar' n (mconcat x:mconcatPar' n r)

toMIPar :: forall (target :: Symbol). (KnownSymbol target) => SMTString -> MI target SMTString 
toMIPar input = undefined 

toMI :: forall (target :: Symbol). (KnownSymbol target) => SMTString -> MI target SMTString 
toMI input = if isNullString input then mempty else  MI input (makeIndices input (fromString (symbolVal (Proxy :: Proxy target))) 0 (stringLen input - 1))

getIndex :: forall (target :: Symbol).  MI target SMTString -> List Int 
getIndex (MI _ i) = i 

clone :: Int -> [a] -> [a]
clone i xs | i <= 0 = [] 
clone 1 xs = xs 
clone n xs = xs ++ clone (n-1) xs

mconcat :: forall (target :: Symbol). (KnownSymbol target) => [MI target SMTString] -> MI target SMTString
mconcat []       = mempty 
mconcat [x]      = x 
mconcat [x1, x2] = mappend x1 x2 
mconcat (x:xs)   = mappend x (mconcat xs)


-- | Indexing Structure Definition 

-- Structure that defines valid indeces of a type level target 
-- symbol in a value level string

data MI (target :: Symbol) s where 
  MI :: SMTString        -- input string
     -> (List Int)      -- valid indeces of target in input
     -> MI target s
  deriving (Show)

{-@ data MI target s 
  = MI { input :: SMTString
       , idxes   :: List Int 
       } @-}


{- data MI target s 
  = MI { input :: SMTString
       , List :: List (GoodIndex input target)
       } @-}


{-@ measure indixesMI @-}
indixesMI (MI _ is) = is 
{-@ measure inputMI @-}
inputMI (MI i _) = i 



{-@ type GoodIndex Input Target 
  = {i:Int |  IsGoodIndex Input Target i}
  @-}

{-@ type GoodIndexTwo Input Input2 Target 
  = {i:Int |  IsGoodIndex Input Target i && IsGoodIndex (concatString Input Input2) Target i }
  @-}

{-@ predicate IsGoodIndex Input Target I
  =  (subString Input I (stringLen Target)  == Target)
  && (I + stringLen Target <= stringLen Input)
  && (0 <= I)
  @-}


-- | Monoid methods 

{-@ reflect mempty @-}
mempty :: forall (target :: Symbol). MI target SMTString
mempty = MI stringEmp N

{-@ reflect mappend @-}
mappend :: forall (target :: Symbol).  (KnownSymbol target) => MI target SMTString -> MI target SMTString -> MI target SMTString
mappend (MI i1 is1) (MI i2 is2)
  = MI (concatString i1 i2) -- (mappendMakeIndixes i1 i2 (fromString (symbolVal (Proxy :: Proxy target))) is1 is2)
    ((is1 
        `append` 
      makeNewIndices i1 i2 (fromString (symbolVal (Proxy :: Proxy target))))
        `append` 
      map (shift (stringLen i1)) is2)            
 

-------------------------------------------------------------------------------
--------------- PROOFS  -------------------------------------------------------
-------------------------------------------------------------------------------

mempty_left :: forall (target :: Symbol). (KnownSymbol target) => MI target SMTString -> Proof
{-@ mempty_left :: xs:MI target SMTString -> {mappend xs mempty == xs } @-}
mempty_left (MI i1 is1)
  =   mappend (MI i1 is1) (mempty :: MI target SMTString)
  ==. mappend (MI i1 is1) (MI stringEmp N) 
  ==. MI (concatString i1 stringEmp)  
       (is1 `append` map (shift (stringLen i1)) N
            `append` makeNewIndices i1 stringEmp (fromString (symbolVal (Proxy :: Proxy target))))
  ==. MI (concatString i1 stringEmp)  
       ((is1 `append` N)
            `append` makeNewIndices i1 stringEmp (fromString (symbolVal (Proxy :: Proxy target))))
  ==. MI (concatString i1 stringEmp)  
       (is1 `append` makeNewIndices i1 stringEmp (fromString (symbolVal (Proxy :: Proxy target))))
      ? appendEmp is1 
  ==. MI (concatString i1 stringEmp)  
       (is1 `append` N) 
      ? makeNewIndicesNullLeft i1 (fromString (symbolVal (Proxy :: Proxy target)))
  ==. MI (concatString i1 stringEmp) is1 
      ? appendEmp is1 
  ==. MI i1 is1 
      ? concatStringNeutral i1 
  *** QED 





mempty_right :: forall (target :: Symbol). (KnownSymbol target) => MI target SMTString -> Proof
{-@ mempty_right :: xs:MI target SMTString -> {mappend mempty xs == xs } @-}
mempty_right (MI i is)
  =   mappend (mempty :: MI target SMTString) (MI i is) 
  ==. mappend (MI stringEmp N) (MI i is) 
  ==. MI (concatString stringEmp i)  
       (N `append` makeNewIndices stringEmp i (fromString (symbolVal (Proxy :: Proxy target)))
               `append` map (shift (stringLen stringEmp)) is)
  ==. MI (concatString stringEmp i)  
       ( makeNewIndices stringEmp i (fromString (symbolVal (Proxy :: Proxy target)))
        `append`
         map (shift (stringLen stringEmp)) is)
  ==. MI (concatString stringEmp i)  
       ( makeNewIndices stringEmp i (fromString (symbolVal (Proxy :: Proxy target)))
         `append` 
         map (shift 0) is)
  ==. MI (concatString stringEmp i)  
       (makeNewIndices stringEmp i (fromString (symbolVal (Proxy :: Proxy target)))
        `append` 
        is)
       ? mapShiftZero is 
  ==. MI (concatString stringEmp i)  
       (N `append` is) 
      ? makeNewIndicesNullRight i (fromString (symbolVal (Proxy :: Proxy target)))
  ==. MI (concatString stringEmp i) is 
  ==. MI i is 
      ? concatStringNeutralRight i
  *** QED 

{-@ mappend_assoc 
  :: x:MI target SMTString -> y:MI target SMTString -> z:MI target SMTString
  -> {v:Proof | mappend x (mappend y z) = mappend (mappend x y) z}
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
                    `append` makeNewIndices yi zi (fromString (symbolVal (Proxy :: Proxy target))))
                    `append` map (shift (stringLen yi)) zis))
  ==. MI (concatString xi (concatString yi zi))  
         ((xis `append` 
               makeNewIndices xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target))))
               `append` 
                  map (shift (stringLen xi)) 
                  ((yis 
                    `append` makeNewIndices yi zi (fromString (symbolVal (Proxy :: Proxy target))))
                    `append` map (shift (stringLen yi)) zis)
              )
  ==. MI (concatString (concatString xi yi) zi)  
         ((xis `append` 
               makeNewIndices xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target))))
               `append` 
                  map (shift (stringLen xi)) 
                  ((yis 
                    `append` makeNewIndices yi zi (fromString (symbolVal (Proxy :: Proxy target))))
                    `append` map (shift (stringLen yi)) zis)
              )
      ? concatStringAssoc xi yi zi 
  ==. MI (concatString (concatString xi yi) zi)  
         ((xis `append` 
               makeNewIndices xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target))))
               `append` 
                  (
                    (map (shift (stringLen xi)) (yis 
                    `append` makeNewIndices yi zi (fromString (symbolVal (Proxy :: Proxy target)))))
                    `append` 
                    map (shift (stringLen xi)) (map (shift (stringLen yi)) zis))
              )
      ? map_append (shift (stringLen xi)) 
                   (yis `append` makeNewIndices yi zi (fromString (symbolVal (Proxy :: Proxy target)))) 
                   (map (shift (stringLen yi)) zis)
  ==. MI (concatString (concatString xi yi) zi)  
         ((xis `append` 
               makeNewIndices xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target))))
               `append` 
                  (
                    (map (shift (stringLen xi)) yis 
                    `append` (map (shift (stringLen xi)) (makeNewIndices yi zi (fromString (symbolVal (Proxy :: Proxy target))))))
                    `append` 
                    map (shift (stringLen xi)) (map (shift (stringLen yi)) zis))
              )
      ? map_append (shift (stringLen xi)) yis (makeNewIndices yi zi (fromString (symbolVal (Proxy :: Proxy target))))
  ==. MI (concatString (concatString xi yi) zi)  
         ((xis `append` 
               makeNewIndices xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target))))
               `append` 
                  (
                    (map (shift (stringLen xi)) yis 
                    `append` (map (shift (stringLen xi)) (makeNewIndices yi zi (fromString (symbolVal (Proxy :: Proxy target))))))
                    `append` 
                    map (shift (stringLen (concatString xi yi))) zis)
              )
      ? map_len_fusion xi yi zis 
-- ((x1~x2) ~ ((x3~x4) ~ x5))
-- == 
--   ((((x1~x2) ~x3) ~x4) ~x5
  ==. MI (concatString (concatString xi yi) zi)
         (((( xis 
               `append` 
              makeNewIndices xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target))))                      `append` map (shift (stringLen xi)) yis)
               `append` 
              map (shift (stringLen xi)) yis)
               `append`
              map (shift (stringLen (concatString xi yi))) zis)

      ? appendReorder xis
                      (makeNewIndices xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target))))
                      (map (shift (stringLen xi)) yis)
                      (map (shift (stringLen xi)) (makeNewIndices yi zi (fromString (symbolVal (Proxy :: Proxy target)))))
                      (map (shift (stringLen (concatString xi yi))) zis)
-- ((((x1 ~ x2) ~ x3) ~ x4) ~ x5)
-- 
-- ((((x1 ~ x2) ~ x3) ~ x4) ~ x5)

  ==. MI (concatString (concatString xi yi) zi)
         (((( xis 
               `append` 
              makeNewIndices xi yi (fromString (symbolVal (Proxy :: Proxy target))))
               `append` 
              map (shift (stringLen xi)) yis)
               `append`
              makeNewIndices (concatString xi yi) zi (fromString (symbolVal (Proxy :: Proxy target))))
               `append` 
              map (shift (stringLen (concatString xi yi))) zis 
          )
      ? shiftIndexes xi yi zi (fromString (symbolVal (Proxy :: Proxy target)))
  ==. mappend (MI (concatString xi yi)  
                  ( (xis `append` makeNewIndices xi yi (fromString (symbolVal (Proxy :: Proxy target))))
                       `append` map (shift (stringLen xi)) yis
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
                    `append` makeNewIndices yi zi (fromString (symbolVal (Proxy :: Proxy target))))
                    `append` map (shift (stringLen yi)) zis))
  ==. MI (concatString xi (concatString yi zi))  
         ((xis `append` 
               makeNewIndices xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target))))
               `append` 
                  map (shift (stringLen xi)) 
                  ((yis 
                    `append` makeNewIndices yi zi (fromString (symbolVal (Proxy :: Proxy target))))
                    `append` map (shift (stringLen yi)) zis)
              )
  ==. MI (concatString (concatString xi yi) zi)  
         ((xis `append` 
               makeNewIndices xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target))))
               `append` 
                  map (shift (stringLen xi)) 
                  ((yis 
                    `append` makeNewIndices yi zi (fromString (symbolVal (Proxy :: Proxy target))))
                    `append` map (shift (stringLen yi)) zis)
              )
      ? concatStringAssoc xi yi zi 
  ==. MI (concatString (concatString xi yi) zi)  
         ((xis `append` 
               makeNewIndices xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target))))
               `append` 
                  map (shift (stringLen xi)) 
                  ((N 
                    `append` makeNewIndices yi zi (fromString (symbolVal (Proxy :: Proxy target))))
                    `append` map (shift (stringLen yi)) zis)
              )
        ? emptyIndexes y (assumeGoodIndex yi (fromString (symbolVal (Proxy :: Proxy target))) yis)
  ==. MI (concatString (concatString xi yi) zi)  
         ((xis `append` 
               makeNewIndices xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target))))
               `append` 
                  map (shift (stringLen xi)) 
                  (makeNewIndices yi zi (fromString (symbolVal (Proxy :: Proxy target)))
                    `append` map (shift (stringLen yi)) zis)
              )
  ==. MI (concatString (concatString xi yi) zi)  
         ((xis `append` 
               makeNewIndices xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target))))
               `append` 
                  (map (shift (stringLen xi)) (makeNewIndices yi zi (fromString (symbolVal (Proxy :: Proxy target))))
                  `append` map (shift (stringLen xi)) (map (shift (stringLen yi)) zis))
              )
      ? map_append (shift (stringLen xi)) 
                   (makeNewIndices yi zi (fromString (symbolVal (Proxy :: Proxy target)))) 
                   (map (shift (stringLen yi)) zis)

  ==. MI (concatString (concatString xi yi) zi)  
         ((xis `append` 
               makeNewIndices xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target))))
               `append` 
                  (map (shift (stringLen xi)) (makeNewIndices yi zi (fromString (symbolVal (Proxy :: Proxy target))))
                  `append` map (shift (stringLen xi)) (map (shift (stringLen yi)) zis))
              )
      ? map_len_fusion xi yi zis 
-- ((x1~x2) ~ (x3~x4))
-- == 
-- (x1 ~ (x2~x3)) ~ x4
  ==. MI (concatString (concatString xi yi) zi)  
         ((xis `append` 
               (makeNewIndices xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target)))
               `append` 
                map (shift (stringLen xi)) (makeNewIndices yi zi (fromString (symbolVal (Proxy :: Proxy target)))))
                  `append` map (shift (stringLen xi)) (map (shift (stringLen yi)) zis))
              )
      ? appendGroupNew xis
                       (makeNewIndices xi (concatString yi zi) (fromString (symbolVal (Proxy :: Proxy target))))
                       (map (shift (stringLen xi)) (makeNewIndices yi zi (fromString (symbolVal (Proxy :: Proxy target)))))
                       (map (shift (stringLen xi)) (map (shift (stringLen yi)) zis))


  ==. MI (concatString (concatString xi yi) zi)  
         ((xis `append` 
               (makeNewIndices xi yi (fromString (symbolVal (Proxy :: Proxy target)))
               `append` 
                makeNewIndices (concatString xi yi) zi (fromString (symbolVal (Proxy :: Proxy target))))
                  `append` map (shift (stringLen xi)) (map (shift (stringLen yi)) zis))
              )
      ? shiftNewIndexes xi yi zi (fromString (symbolVal (Proxy :: Proxy target)))
  ==. MI (concatString (concatString xi yi) zi)  
         ((xis `append` 
               (makeNewIndices xi yi (fromString (symbolVal (Proxy :: Proxy target)))
               `append` 
                makeNewIndices (concatString xi yi) zi (fromString (symbolVal (Proxy :: Proxy target))))
                  `append` map (shift (stringLen (concatString xi yi))) zis)
              )
      ? map_len_fusion xi yi zis 

-- (x1 ~ (x2 ~ x3)) ~ x4 == ((x1 ~ x2) ~ x3) ~ x4
  ==. MI (concatString (concatString xi yi) zi)  
         (((xis `append` makeNewIndices xi yi (fromString (symbolVal (Proxy :: Proxy target))))
         `append`
            (makeNewIndices (concatString xi yi) zi (fromString (symbolVal (Proxy :: Proxy target)))))
         `append` 
            map (shift (stringLen (concatString xi yi))) zis )
      ? appendUnGroupNew xis 
                         (makeNewIndices xi yi (fromString (symbolVal (Proxy :: Proxy target))))
                         (makeNewIndices (concatString xi yi) zi (fromString (symbolVal (Proxy :: Proxy target))))
                         (map (shift (stringLen (concatString xi yi))) zis)

  ==. MI (concatString (concatString xi yi) zi)  
        ((((xis `append` makeNewIndices xi yi (fromString (symbolVal (Proxy :: Proxy target))))
                       `append` N
                  )
         `append`
            (makeNewIndices (concatString xi yi) zi (fromString (symbolVal (Proxy :: Proxy target)))))
         `append` 
            map (shift (stringLen (concatString xi yi))) zis )
          ? appendEmp (xis `append` makeNewIndices xi yi (fromString (symbolVal (Proxy :: Proxy target))))
  ==. MI (concatString (concatString xi yi) zi)  
        ((((xis `append` makeNewIndices xi yi (fromString (symbolVal (Proxy :: Proxy target))))
                       `append` map (shift (stringLen xi)) N
                  )
         `append`
            (makeNewIndices (concatString xi yi) zi (fromString (symbolVal (Proxy :: Proxy target)))))
         `append` 
            map (shift (stringLen (concatString xi yi))) zis )
  ==. MI (concatString (concatString xi yi) zi)  
        ((((xis `append` makeNewIndices xi yi (fromString (symbolVal (Proxy :: Proxy target))))
                       `append` map (shift (stringLen xi)) yis
                  )
         `append`
            (makeNewIndices (concatString xi yi) zi (fromString (symbolVal (Proxy :: Proxy target)))))
         `append` 
            map (shift (stringLen (concatString xi yi))) zis )
      ?emptyIndexes y (assumeGoodIndex yi (fromString (symbolVal (Proxy :: Proxy target))) yis)
  ==. mappend (MI (concatString xi yi)  
                  ( (xis `append` makeNewIndices xi yi (fromString (symbolVal (Proxy :: Proxy target))))
                         `append` map (shift (stringLen xi)) yis
                  )
              ) (MI zi zis)
  ==. mappend (mappend (MI xi xis) (MI yi yis)) (MI zi zis)
  *** QED 

-------------------------------------------------------------------------------
------------------ Helper Proofs ----------------------------------------------
-------------------------------------------------------------------------------


{-@ assumeGoodIndex :: input:SMTString -> target:SMTString -> is:List Int 
                    -> {v:List (GoodIndex input target) | v == is} @-} 
assumeGoodIndex :: SMTString -> SMTString -> List Int -> List Int 
assumeGoodIndex input target is 
  = if isJust (areGoodIndexes input target is) then fromJust (areGoodIndexes input target is) else error ""  


{-@ areGoodIndexes :: input:SMTString -> target:SMTString -> is:List Int 
                   -> Maybe ({v:List (GoodIndex input target) | v == is}) @-} 
areGoodIndexes :: SMTString -> SMTString -> List Int -> Maybe (List Int) 
areGoodIndexes input target N
  = Just N
areGoodIndexes input target (C x xs)
  | isGoodIndex input target x 
  = case areGoodIndexes input target xs of 
       Nothing -> Nothing 
       Just is -> Just (C x is) 
  | otherwise
  = Nothing 

  
emptyIndexes :: forall (target :: Symbol). (KnownSymbol target) => MI target SMTString -> List Int  -> Proof
{-@ emptyIndexes :: mi:MI target SMTString
                 -> is:{List (GoodIndex (inputMI mi) target) | is == indixesMI mi && stringLen (inputMI mi) < stringLen target}
                 -> { is == N } @-}
emptyIndexes (MI _ _) N 
  = trivial 
emptyIndexes (MI _ _) (C _ _)
  = trivial 


{-@ shiftIndexes
  :: xi:SMTString 
  -> yi:SMTString 
  -> zi:SMTString 
  -> tg:{SMTString | stringLen tg <= stringLen yi } 
  -> {  (makeNewIndices xi (concatString yi zi) tg == makeNewIndices xi yi tg)  
        && 
        (map (shift (stringLen xi)) (makeNewIndices yi zi tg) == makeNewIndices (concatString xi yi) zi tg)
     }
  @-}
shiftIndexes :: SMTString -> SMTString -> SMTString -> SMTString -> Proof
shiftIndexes xi yi zi tg = shiftIndexesLeft xi yi zi tg &&& shiftIndexesRight xi yi zi tg 

{-@ reflect chunkString @-}
{-@ chunkString :: Int -> xs:SMTString -> List (SMTString) / [stringLen xs] @-}
chunkString :: Int -> SMTString -> List (SMTString)
chunkString i xs 
  | i <= 0 
  = C xs N 
  | stringLen xs <= i 
  = C xs N 
  | otherwise
  = C (takeString i xs) (chunkString i (dropString i xs))



{-@ shiftIndexesLeft
  :: xi:SMTString 
  -> yi:SMTString 
  -> zi:SMTString 
  -> tg:{SMTString | stringLen tg <= stringLen yi } 
  -> {  makeNewIndices xi (concatString yi zi) tg == makeNewIndices xi yi tg}
  @-}
shiftIndexesLeft :: SMTString -> SMTString -> SMTString -> SMTString -> Proof
shiftIndexesLeft xi yi zi tg
  | stringLen tg < 2 
  =   makeNewIndices xi (concatString yi zi) tg 
  ==. N
  ==. makeNewIndices xi yi tg 
  *** QED 
  | otherwise
  =   makeNewIndices xi (concatString yi zi) tg 
  ==. makeIndices (concatString xi (concatString yi zi)) tg 
                   (maxInt (stringLen xi - (stringLen tg-1)) 0)
                   (stringLen xi - 1)
  ==. makeIndices (concatString (concatString xi yi) zi) tg 
                   (maxInt (stringLen xi - (stringLen tg-1)) 0)
                   (stringLen xi - 1)
     ?concatStringAssoc xi yi zi 
  ==. makeIndices (concatString xi yi) tg 
                   (maxInt (stringLen xi - (stringLen tg-1)) 0)
                   (stringLen xi - 1)                
      ? concatmakeNewIndices (maxInt (stringLen xi - (stringLen tg-1)) 0) (stringLen xi - 1) tg (concatString xi yi) zi 
  ==. makeNewIndices xi yi tg 
  *** QED 



{-@ concatmakeNewIndices
  :: lo:Nat -> hi:Int
  -> target: SMTString
  -> input : {SMTString | hi + stringLen target <= stringLen input } 
  -> input': SMTString   
  -> {  makeIndices (concatString input input') target lo hi == makeIndices input target lo hi }
  / [hi - lo]  @-}
concatmakeNewIndices :: Int -> Int -> SMTString -> SMTString -> SMTString  -> Proof
concatmakeNewIndices lo hi target input input'
  | hi < lo 
  =   makeIndices input target lo hi
  ==. N
  ==. makeIndices (concatString input input') target lo hi 
  *** QED 
  | lo == hi, isGoodIndex input target lo
  =   makeIndices input target lo hi
  ==. lo `C` N
  ==. makeIndices (concatString input input') target lo hi 
      ? isGoodIndexConcatString input input' target lo  
  *** QED 
  | lo == hi
  =  makeIndices input target lo hi 
  ==. N
  ==. makeIndices (concatString input input') target lo hi
      ? isGoodIndexConcatString input input' target lo  
  *** QED 
concatmakeNewIndices lo hi target input input' 
  | isGoodIndex input target lo
  =   makeIndices input target lo hi
  ==. lo `C` (makeIndices input target (lo + 1) hi)
  ==. lo `C` (makeIndices (concatString input input') target (lo + 1) hi)
       ? concatmakeNewIndices (lo+1) hi target input input'
  ==. makeIndices  (concatString input input') target lo hi
      ? isGoodIndexConcatString input input' target lo  
  *** QED 
  | otherwise 
  =   makeIndices input target lo hi
  ==. makeIndices input target (lo + 1) hi
  ==. makeIndices (concatString input input') target (lo + 1) hi
       ? concatmakeNewIndices (lo+1) hi target input input'
  ==. makeIndices  (concatString input input') target lo hi
      ? isGoodIndexConcatString input input' target lo  
  *** QED 



{-@ isGoodIndexConcatFront 
  :: input:SMTString -> input':SMTString -> tg:SMTString -> i:Nat
  -> {((isGoodIndex input tg i) <=> isGoodIndex (concatString input' input) tg (stringLen input' + i) )
     } @-}
isGoodIndexConcatFront :: SMTString -> SMTString -> SMTString -> Int -> Proof 
isGoodIndexConcatFront input input' tg i 
  =   isGoodIndex input tg i 
  ==. (subString input i (stringLen tg)  == tg  
      && i + stringLen tg <= stringLen input 
      && 0 <= i)  
  ==. (subString input i (stringLen tg)  == tg  
      && (stringLen input' + i) + stringLen tg <= stringLen (concatString input' input) 
      && 0 <= i)  
  ==. (subString (concatString input' input) (stringLen input' + i) (stringLen tg)  == tg  
      && (stringLen input' + i) + stringLen tg <= stringLen (concatString input' input) 
      && 0 <= (stringLen input' + i))  
      ? (subStringConcatFront input input' (stringLen tg) i *** QED)
  ==. isGoodIndex (concatString input' input) tg (stringLen input' + i) 
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
  -> { map (shift (stringLen xi)) (makeNewIndices yi zi tg) == makeNewIndices (concatString xi yi) zi tg }
  @-}
shiftIndexesRight :: SMTString -> SMTString -> SMTString -> SMTString -> Proof
shiftIndexesRight xi yi zi tg
  | stringLen tg < 2 
  =   makeNewIndices (concatString xi yi) zi tg 
  ==. N
  ==. map (shift (stringLen xi)) N
  ==. map (shift (stringLen xi)) (makeNewIndices yi zi tg)
  *** QED 
shiftIndexesRight xi yi zi tg
-- NV NV NV 
-- This is suspicious!!! it should require exactly the precondition 
-- || tg || <= || yi || 
--   | stringLen tg  <= stringLen yi + 1 
  =   makeNewIndices (concatString xi yi) zi tg  
  ==. makeIndices (concatString (concatString xi yi) zi) tg 
                   (maxInt (stringLen (concatString xi yi) - (stringLen tg -1)) 0)
                   (stringLen (concatString xi yi) - 1 )
  ==. makeIndices (concatString (concatString xi yi) zi) tg 
                   (stringLen (concatString xi yi) - (stringLen tg -1))
                   (stringLen (concatString xi yi) - 1 )
  ==. makeIndices (concatString (concatString xi yi) zi) tg 
                   (stringLen xi + stringLen yi - stringLen tg + 1)
                   (stringLen xi + stringLen yi - 1 )
  ==. makeIndices (concatString xi (concatString yi zi)) tg 
                   (stringLen xi + stringLen yi - stringLen tg + 1)
                   (stringLen xi + stringLen yi - 1 )
       ?concatStringAssoc xi yi zi
  ==. map (shift (stringLen xi)) (makeIndices (concatString yi zi) tg (stringLen yi - stringLen tg + 1) (stringLen yi - 1))
       ? shiftIndexesRight' (stringLen yi - stringLen tg + 1)
                            (stringLen yi - 1)
                            xi 
                            (concatString yi zi)
                            tg 
  ==. map (shift (stringLen xi)) 
               (makeIndices (concatString yi zi) tg 
                             (maxInt (stringLen yi - (stringLen tg -1)) 0)
                             (stringLen yi -1))
  ==. map (shift (stringLen xi)) 
               (makeNewIndices yi zi tg)
  *** QED

{-@ shiftIndexesRight'
  :: lo:Nat 
  -> hi:Int  
  -> x:SMTString 
  -> input:SMTString 
  -> tg:SMTString
  -> { map (shift (stringLen x)) (makeIndices input tg lo hi) == makeIndices (concatString x input) tg (stringLen x + lo) (stringLen x + hi) }
  / [if hi < lo then 0 else  hi-lo]
  @-}
shiftIndexesRight' :: Int -> Int -> SMTString -> SMTString -> SMTString -> Proof
shiftIndexesRight' lo hi x input target
  | hi < lo 
  =   map (shift (stringLen x)) (makeIndices input target lo hi)
  ==. map (shift (stringLen x)) N
  ==. N
  ==. makeIndices (concatString x input) target (stringLen x + lo) (stringLen x + hi)
  *** QED 
  | lo == hi, isGoodIndex input target lo 
  =   map (shift (stringLen x)) (makeIndices input target lo hi)
  ==. map (shift (stringLen x)) (lo `C` N)
  ==. ((shift (stringLen x)) lo) `C` (map (shift (stringLen x)) N)
  ==. (stringLen x + lo) `C` N
  ==. makeIndices (concatString x input) target (stringLen x + lo) (stringLen x + hi)
     ? isGoodIndexConcatFront input x target lo  -- ( => IsGoodIndex (concatString x input) target (stringLen x + lo))
  *** QED 
  | lo == hi
  =   map (shift (stringLen x)) (makeIndices input target lo hi)
  ==. map (shift (stringLen x)) N
  ==. N
  ==. makeIndices (concatString x input) target (stringLen x + lo) (stringLen x + hi)
     ? (isGoodIndexConcatFront input x target lo *** QED)
  *** QED 

shiftIndexesRight' lo hi x input target
  | isGoodIndex input target lo
  =   map (shift (stringLen x)) (makeIndices input target lo hi)
  ==. map (shift (stringLen x)) (lo `C`(makeIndices input target (lo+1) hi))
  ==. (shift (stringLen x) lo) `C` (map (shift (stringLen x)) (makeIndices input target (lo+1) hi))
  ==. (shift (stringLen x) lo) `C` (makeIndices (concatString x input) target (stringLen x + (lo+1)) (stringLen x + hi))
      ? shiftIndexesRight' (lo+1) hi x input target
  ==. (stringLen x + lo) `C` (makeIndices (concatString x input) target (stringLen x + (lo+1)) (stringLen x + hi))
  ==. makeIndices (concatString x input) target (stringLen x + lo) (stringLen x + hi)
     ? (isGoodIndexConcatFront input x target lo *** QED)
  *** QED 
  | otherwise
  =   map (shift (stringLen x)) (makeIndices input target lo hi)
  ==. map (shift (stringLen x)) (makeIndices input target (lo + 1) hi)
  ==. makeIndices (concatString x input) target (stringLen x + (lo+1)) (stringLen x + hi)
      ? shiftIndexesRight' (lo+1) hi x input target
  ==. makeIndices (concatString x input) target (stringLen x + lo) (stringLen x + hi)
     ? (isGoodIndexConcatFront input x target lo *** QED)
  *** QED 


{-@ shiftNewIndexes
  :: xi:SMTString 
  -> yi:SMTString 
  -> zi:SMTString 
  -> tg:{SMTString | stringLen yi < stringLen tg  } 
  -> {  append (makeNewIndices xi (concatString yi zi) tg) (map (shift (stringLen xi)) (makeNewIndices yi zi tg)) == append (makeNewIndices xi yi tg) (makeNewIndices (concatString xi yi) zi tg)
     }
  @-}
shiftNewIndexes :: SMTString -> SMTString -> SMTString -> SMTString -> Proof
shiftNewIndexes xi yi zi tg 
  | stringLen tg < 2 
  =   append (makeNewIndices xi (concatString yi zi) tg) (map (shift (stringLen xi)) (makeNewIndices yi zi tg)) 
  ==. append N (map (shift (stringLen xi)) N) 
  ==. map (shift (stringLen xi)) N 
  ==. N 
  ==. append N N
  ==. append (makeNewIndices xi yi tg) (makeNewIndices (concatString xi yi) zi tg)
  *** QED 

shiftNewIndexes xi yi zi tg 
  | stringLen xi == 0 
  =   append (makeNewIndices xi (concatString yi zi) tg) 
                  (map (shift (stringLen xi)) (makeNewIndices yi zi tg))
  ==. append (makeNewIndices stringEmp (concatString yi zi) tg) 
                  (map (shift (stringLen xi)) (makeNewIndices yi zi tg))
  ? stringEmpProp xi 
  ==. append (makeNewIndices stringEmp (concatString yi zi) tg) 
                  (map (shift (stringLen xi)) (makeNewIndices yi zi tg))
  ? makeNewIndicesNullRight (concatString yi zi) tg
  ==. append N
                  (map (shift (stringLen xi)) (makeNewIndices yi zi tg))
  ==. map (shift (stringLen xi)) (makeNewIndices yi zi tg)
  ==. map (shift 0) (makeNewIndices yi zi tg)
      ? mapShiftZero (makeNewIndices yi zi tg)
  ==. makeNewIndices yi zi tg
  ==. makeNewIndices (concatString xi yi) zi tg
        ? concatEmpLeft xi yi 
  ==. append N (makeNewIndices (concatString xi yi) zi tg)
  ==. append (makeNewIndices stringEmp yi tg) (makeNewIndices (concatString xi yi) zi tg)
       ? makeNewIndicesNullRight yi tg
  ==. append (makeNewIndices xi yi tg) (makeNewIndices (concatString xi yi) zi tg)
      ? stringEmpProp xi
  *** QED 
  | stringLen yi == 0 
  =   append (makeNewIndices xi (concatString yi zi) tg) 
                  (map (shift (stringLen xi)) (makeNewIndices yi zi tg))
  ==. append (makeNewIndices xi zi tg) 
                  (map (shift (stringLen xi)) (makeNewIndices yi zi tg))
      ? concatEmpLeft yi zi 
  ==. append (makeNewIndices xi zi tg) 
                  (map (shift (stringLen xi)) (makeNewIndices stringEmp zi tg))
      ? stringEmpProp yi
  ==. append (makeNewIndices xi zi tg) 
                  (map (shift (stringLen xi)) N)
      ? makeNewIndicesNullRight zi tg 
  ==. append (makeNewIndices xi zi tg) 
                  N
  ==. makeNewIndices xi zi tg 
       ?appendEmp (makeNewIndices xi zi tg)
  ==. makeNewIndices (concatString xi yi) zi tg
       ? concatEmpRight xi yi
  ==. append N (makeNewIndices (concatString xi yi) zi tg)
  ==. append (makeNewIndices xi stringEmp tg) (makeNewIndices (concatString xi yi) zi tg)
       ? makeNewIndicesNullLeft xi tg 
  ==. append (makeNewIndices xi yi tg) (makeNewIndices (concatString xi yi) zi tg)
       ? stringEmpProp yi
  *** QED 
  | stringLen yi - stringLen tg == -1 
  = let minidx = maxInt (stringLen xi - stringLen tg + 1) 0 in 
      append (makeNewIndices xi (concatString yi zi) tg) 
                  (map (shift (stringLen xi)) (makeNewIndices yi zi tg)) 
  ==. append (makeIndices (concatString xi (concatString yi zi)) tg
                                (maxInt (stringLen xi - stringLen tg + 1) 0)
                                (stringLen xi -1)) 
                  (map (shift (stringLen xi)) 
                            (makeIndices (concatString yi zi) tg
                                          (maxInt (stringLen yi - stringLen tg +1) 0)
                                          (stringLen yi -1)
                            )) 
  ==. append (makeIndices (concatString xi (concatString yi zi)) tg
                                (maxInt (stringLen xi - stringLen tg + 1) 0)
                                (stringLen xi -1)) 
                  (map (shift (stringLen xi)) 
                            (makeIndices (concatString yi zi) tg
                                          (maxInt 0 0)
                                          (stringLen yi -1)
                            )) 
  ==. append (makeIndices (concatString xi (concatString yi zi)) tg
                                (maxInt (stringLen xi - stringLen tg + 1) 0)
                                (stringLen xi -1)) 
                  (map (shift (stringLen xi)) 
                            (makeIndices (concatString yi zi) tg
                                          0
                                          (stringLen yi -1)
                            )) 
  ==. append (makeIndices (concatString xi (concatString yi zi)) tg
                                minidx
                                (stringLen xi -1)) 
                  (makeIndices (concatString xi (concatString yi zi)) tg 
                                (stringLen xi) 
                                (stringLen xi + stringLen yi -1)) 
      ? shiftIndexesRight' 0 (stringLen yi -1) xi (concatString yi zi) tg 
  ==. append (makeIndices (concatString (concatString xi yi) zi) tg
                                minidx
                                (stringLen xi -1)) 
                  (makeIndices (concatString (concatString xi yi) zi) tg 
                                (stringLen xi) 
                                (stringLen xi + stringLen yi -1)) 
      ? concatStringAssoc xi yi zi 

  ==. append (append 

                  (makeIndices (concatString (concatString xi yi) zi) tg
                                minidx
                                (stringLen xi + stringLen yi - stringLen tg))

                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (stringLen xi)
                                (stringLen xi -1))

                                ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg 
                                (stringLen xi)
                                (stringLen xi + stringLen yi -1)) 
      ? mergeIndixes (concatString (concatString xi yi) zi) tg 
                     minidx -- maxInt (stringLen xi - stringLen tg + 1) 0
                     (stringLen xi -1)
                     (stringLen xi -1)
  ==. append (append 

                  (makeIndices (concatString (concatString xi yi) zi) tg
                                minidx
                                (stringLen xi + stringLen yi - stringLen tg))

                  N

                                ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg 
                                (stringLen xi)
                                (stringLen xi + stringLen yi -1)) 
  ==. append (makeIndices (concatString (concatString xi yi) zi) tg
                                minidx
                                (stringLen xi + stringLen yi - stringLen tg))
                  (makeIndices (concatString (concatString xi yi) zi) tg 
                                (stringLen xi)
                                (stringLen xi + stringLen yi -1)) 
      ?appendEmp (makeIndices (concatString (concatString xi yi) zi) tg
                                    minidx
                                    (stringLen xi + stringLen yi - stringLen tg))
  ==. append (makeIndices (concatString (concatString xi yi) zi) tg
                                minidx
                                (stringLen xi -1))

                  (makeIndices (concatString (concatString xi yi) zi) tg
                                ((stringLen xi))
                                (stringLen xi + stringLen yi -1))
  ==. append (makeIndices (concatString (concatString xi yi) zi) tg
                                minidx 
                                (stringLen (concatString xi yi)  - stringLen tg))

                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (stringLen xi)
                                (stringLen xi + stringLen yi -1))

  ==. append (makeIndices (concatString xi yi) tg 
                                minidx
                                (stringLen xi-1)
                  ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (stringLen xi)
                                (stringLen xi + stringLen yi  - 1)
                  )
      ? catIndixes (concatString xi yi) zi tg minidx (stringLen xi-1)
  ==. append (makeIndices (concatString xi yi) tg 
                                minidx 
                                -- maxInt (stringLen xi - stringLen tg + 1) 0 && 2 <= stringLen tg
                                (stringLen xi-1)
                  ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (stringLen xi)
                                (stringLen xi + stringLen yi  - 1)
                  )

  ==. append (makeIndices (concatString xi yi) tg 
                                minidx
                                (stringLen xi-1)
                  ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (maxInt (stringLen xi) 0)
                                (stringLen xi + stringLen yi  - 1)
                  )


  ==. append (makeIndices (concatString xi yi) tg 
                                minidx
                                (stringLen xi-1)
                  ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (maxInt (stringLen xi + stringLen yi - stringLen tg + 1) 0)
                                (stringLen xi + stringLen yi  - 1)
                  )

  ==. append (makeIndices (concatString xi yi) tg 
                                minidx
                                (stringLen xi-1)
                  ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (maxInt (stringLen (concatString xi yi) - stringLen tg + 1) 0)
                                (stringLen (concatString xi yi) - 1)
                  )
  ==. append (makeIndices (concatString xi yi) tg 
                                (maxInt (stringLen xi - stringLen tg +1) 0)
                                (stringLen xi-1)
                  ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (maxInt (stringLen (concatString xi yi) - stringLen tg + 1) 0)
                                (stringLen (concatString xi yi) - 1)
                  )
  ==. append (makeNewIndices xi yi tg) (makeNewIndices (concatString xi yi) zi tg)
  *** QED 
shiftNewIndexes xi yi zi tg 
-- THIS ALWAYS HOLDS 
--   | stringLen yi + 1 <= stringLen tg
  | 0 <= stringLen xi + stringLen yi - stringLen tg
 --  , 0 < stringLen xi 
  = let minidx = maxInt (stringLen xi - stringLen tg + 1) 0 in 
      append (makeNewIndices xi (concatString yi zi) tg) 
                  (map (shift (stringLen xi)) (makeNewIndices yi zi tg)) 
  ==. append (makeIndices (concatString xi (concatString yi zi)) tg
                                (maxInt (stringLen xi - stringLen tg + 1) 0)
                                (stringLen xi -1)) 
                  (map (shift (stringLen xi)) 
                            (makeIndices (concatString yi zi) tg
                                          (maxInt (stringLen yi - stringLen tg +1) 0)
                                          (stringLen yi -1)
                            )) 
  ==. append (makeIndices (concatString xi (concatString yi zi)) tg
                                minidx
                                (stringLen xi -1)) 
                  (map (shift (stringLen xi)) 
                            (makeIndices (concatString yi zi) tg
                                           0
                                          (stringLen yi -1)
                            )) 
  ==. append (makeIndices (concatString xi (concatString yi zi)) tg
                                minidx
                                (stringLen xi -1)) 
                  (makeIndices (concatString xi (concatString yi zi)) tg 
                                (stringLen xi) 
                                (stringLen xi + stringLen yi -1)) 
      ? shiftIndexesRight' 0 (stringLen yi -1) xi (concatString yi zi) tg 
  ==. append (makeIndices (concatString (concatString xi yi) zi) tg
                                minidx
                                (stringLen xi -1)) 
                  (makeIndices (concatString (concatString xi yi) zi) tg 
                                (stringLen xi) 
                                (stringLen xi + stringLen yi -1)) 
      ? concatStringAssoc xi yi zi 

  ==. append (append 

                  (makeIndices (concatString (concatString xi yi) zi) tg
                                minidx
                                (stringLen xi + stringLen yi - stringLen tg))

                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (stringLen xi + stringLen yi - stringLen tg + 1)
                                (stringLen xi -1))

                                ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg 
                                (stringLen xi)
                                (stringLen xi + stringLen yi -1)) 
      ? mergeIndixes (concatString (concatString xi yi) zi) tg 
                     minidx -- maxInt (stringLen xi - stringLen tg + 1) 0
                     (stringLen xi + stringLen yi - stringLen tg)
                     (stringLen xi -1)
  ==. append (makeIndices (concatString (concatString xi yi) zi) tg
                                minidx 
                                (stringLen xi + stringLen yi - stringLen tg))

                 (append

                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (stringLen xi + stringLen yi - stringLen tg +1)
                                (stringLen xi -1))

                                
                  (makeIndices (concatString (concatString xi yi) zi) tg 
                                (stringLen xi)
                                (stringLen xi + stringLen yi -1)) )
      ? appendAssoc
              (makeIndices (concatString (concatString xi yi) zi) tg
                                minidx
                                (stringLen xi + stringLen yi - stringLen tg))
              (makeIndices (concatString (concatString xi yi) zi) tg
                                (stringLen xi + stringLen yi - stringLen tg+1)
                                (stringLen xi -1))
              (makeIndices (concatString (concatString xi yi) zi) tg 
                                (stringLen xi)
                                (stringLen xi + stringLen yi -1))

  ==. append (makeIndices (concatString (concatString xi yi) zi) tg
                                minidx
                                (stringLen xi + stringLen yi - stringLen tg))

                  (makeIndices (concatString (concatString xi yi) zi) tg
                                ((stringLen xi + stringLen yi - stringLen tg+1))
                                (stringLen xi + stringLen yi -1))
     ? mergeIndixes (concatString (concatString xi yi) zi) tg 
                  ((stringLen xi + stringLen yi - stringLen tg+1))
                  (stringLen xi-1)
                  (stringLen xi + stringLen yi -1)

  ==. append (makeIndices (concatString (concatString xi yi) zi) tg
                                minidx 
                                (stringLen (concatString xi yi)  - stringLen tg))

                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (stringLen xi + stringLen yi - stringLen tg + 1)
                                (stringLen xi + stringLen yi -1))

  ==. append (makeIndices (concatString xi yi) tg 
                                minidx
                                (stringLen xi-1)
                  ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (stringLen xi + stringLen yi - stringLen tg + 1)
                                (stringLen xi + stringLen yi  - 1)
                  )
      ? catIndixes (concatString xi yi) zi tg minidx (stringLen xi-1)

  ==. append (makeIndices (concatString xi yi) tg 
                                minidx
                                (stringLen xi-1)
                  ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (maxInt (stringLen xi + stringLen yi - stringLen tg + 1) 0)
                                (stringLen xi + stringLen yi  - 1)
                  )

  ==. append (makeIndices (concatString xi yi) tg 
                                minidx
                                (stringLen xi-1)
                  ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (maxInt (stringLen (concatString xi yi) - stringLen tg + 1) 0)
                                (stringLen (concatString xi yi) - 1)
                  )
  ==. append (makeIndices (concatString xi yi) tg 
                                (maxInt (stringLen xi - stringLen tg +1) 0)
                                (stringLen xi-1)
                  ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (maxInt (stringLen (concatString xi yi) - stringLen tg + 1) 0)
                                (stringLen (concatString xi yi) - 1)
                  )
  ==. append (makeNewIndices xi yi tg) (makeNewIndices (concatString xi yi) zi tg)
  *** QED 

--   | stringLen yi + 1 <= stringLen tg
  | stringLen xi + stringLen yi < stringLen tg
  =   append (makeNewIndices xi (concatString yi zi) tg) 
                  (map (shift (stringLen xi)) (makeNewIndices yi zi tg)) 
  ==. append (makeIndices (concatString xi (concatString yi zi)) tg
                                (maxInt (stringLen xi - stringLen tg + 1) 0)
                                (stringLen xi -1)) 
                  (map (shift (stringLen xi)) 
                            (makeIndices (concatString yi zi) tg
                                          (maxInt (stringLen yi - stringLen tg +1) 0)
                                          (stringLen yi -1)
                            )) 
  ==. append (makeIndices (concatString xi (concatString yi zi)) tg
                                0
                                (stringLen xi -1)) 
                  (map (shift (stringLen xi)) 
                            (makeIndices (concatString yi zi) tg
                                           0
                                          (stringLen yi -1)
                            )) 
  ==. append (makeIndices (concatString xi (concatString yi zi)) tg
                                0
                                (stringLen xi -1)) 
                  (makeIndices (concatString xi (concatString yi zi)) tg 
                                (stringLen xi) 
                                (stringLen xi + stringLen yi -1)) 
      ? shiftIndexesRight' 0 (stringLen yi -1) xi (concatString yi zi) tg 
  ==. append (makeIndices (concatString (concatString xi yi) zi) tg
                                0
                                (stringLen xi -1)) 
                  (makeIndices (concatString (concatString xi yi) zi) tg 
                                (stringLen xi) 
                                (stringLen xi + stringLen yi -1)) 
      ? concatStringAssoc xi yi zi 

  ==. makeIndices (concatString (concatString xi yi) zi) tg
                                0
                                (stringLen (concatString xi yi) - 1)
      ?mergeIndixes (concatString (concatString xi yi) zi) tg 
                    0 
                    (stringLen xi-1) 
                    (stringLen (concatString xi yi) -1)

  ==. append N 
                  (makeIndices (concatString (concatString xi yi) zi) tg
                                0
                                (stringLen (concatString xi yi) - 1)
                  )

  ==. append (makeIndices (concatString xi yi) tg 
                                0
                                (stringLen xi-1)
                  ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg
                                0
                                (stringLen (concatString xi yi) - 1)
                  )
      ? smallInput (concatString xi yi) tg 0 (stringLen xi -1)
  ==. append (makeIndices (concatString xi yi) tg 
                                (maxInt (stringLen xi - stringLen tg +1) 0)
                                (stringLen xi-1)
                  ) 
                  (makeIndices (concatString (concatString xi yi) zi) tg
                                (maxInt (stringLen (concatString xi yi) - stringLen tg + 1) 0)
                                (stringLen (concatString xi yi) - 1)
                  )
  ==. append (makeNewIndices xi yi tg) (makeNewIndices (concatString xi yi) zi tg)
  *** QED 

-- NIKI CHECK: Feels have done this proof before 
maxIndixes 
  :: SMTString -> SMTString -> Int -> Int -> Proof 
{-@ maxIndixes 
  :: input:SMTString -> target:SMTString -> lo:{Nat | stringLen input < lo + stringLen target} -> hi:Int
  -> {makeIndices input target lo hi = N}
  / [hi - lo ] @-}
maxIndixes input target lo hi 
  | hi < lo 
  =   makeIndices input target lo hi  
  ==. N
  *** QED 
  | lo == hi, not (isGoodIndex input target lo)
  =   makeIndices input target lo hi  
  ==. N
  *** QED 
  | not (isGoodIndex input target lo)
  =   makeIndices input target lo hi
  ==. N 
  ==. makeIndices input target (lo+1) hi 
      ? maxIndixes input target (lo+1) hi 
  *** QED 


mergeIndixes :: SMTString -> SMTString -> Int -> Int -> Int -> Proof
{-@ mergeIndixes 
  :: input:SMTString -> target:SMTString -> lo:Nat -> mid:{Int | lo <= mid} -> hi:{Int | mid <= hi} 
  -> {makeIndices input target lo hi == append (makeIndices input target lo mid) (makeIndices input target (mid+1) hi)} 
  / [mid] @-}
mergeIndixes input target lo mid hi 
  | lo == mid, isGoodIndex input target lo 
  =   append (makeIndices input target lo mid) (makeIndices input target (mid+1) hi)
  ==. append (makeIndices input target lo lo)  (makeIndices input target (mid+1) hi)
  ==. append (lo `C` N)  (makeIndices input target (mid+1) hi)
  ==. lo  `C` (append N  (makeIndices input target (lo+1) hi))
  ==. lo  `C` (makeIndices input target (lo+1) hi)
  ==. makeIndices input target lo hi
  *** QED 
  | lo == mid, not (isGoodIndex input target lo)
  =   append (makeIndices input target lo mid) (makeIndices input target (mid+1) hi)
  ==. append (makeIndices input target lo lo)  (makeIndices input target (mid+1) hi)
  ==. append (lo `C` N)  (makeIndices input target (mid+1) hi)
  ==. (append N  (makeIndices input target (lo+1) hi))
  ==. makeIndices input target lo hi
  *** QED 
  | lo < mid, not (isGoodIndex input target mid)
  =   makeIndices input target lo hi
  ==. append (makeIndices input target lo (mid-1)) 
                  (makeIndices input target mid hi)
       ? mergeIndixes input target lo (mid-1) hi 

  ==. append (makeIndices input target lo (mid-1)) 
                  (makeIndices input target (mid+1) hi)

  ==. append (makeIndices input target lo mid) 
                  (makeIndices input target (mid+1) hi)
      ?makeNewIndicesBadLast input target lo mid
  *** QED 
  | lo < mid, isGoodIndex input target mid
  =   makeIndices input target lo hi
  ==. append (makeIndices input target lo (mid-1)) 
                  (makeIndices input target mid hi)
       ? mergeIndixes input target lo (mid-1) hi 

  ==. append (makeIndices input target lo (mid-1)) 
                  (mid `C` makeIndices input target (mid+1) hi)


  ==. append (makeIndices input target lo (mid-1)) 
                  (mid `C` (append N (makeIndices input target (mid+1) hi)))

  ==. append (makeIndices input target lo (mid-1)) 
                  (append (C mid N) (makeIndices input target (mid+1) hi))

  ==. append (append (makeIndices input target lo (mid-1)) (C mid N)) 
                  (makeIndices input target (mid+1) hi)
      ? appendAssoc (makeIndices input target lo (mid-1)) (C mid N) (makeIndices input target (mid+1) hi)

  ==. append (makeIndices input target lo mid) 
                  (makeIndices input target (mid+1) hi)
      ?makeNewIndicesGoodLast input target lo mid
  *** QED 


makeNewIndicesGoodLast, makeNewIndicesBadLast 
  :: SMTString -> SMTString -> Int -> Int -> Proof 
{-@ makeNewIndicesGoodLast 
  :: input:SMTString -> target:SMTString -> lo:Nat -> hi:{Int | lo <= hi && (isGoodIndex input target hi)}
  -> {makeIndices input target lo hi == append (makeIndices input target lo (hi-1)) (C hi N)}
  / [hi - lo] @-}
makeNewIndicesGoodLast input target lo hi 
  | lo == hi, (isGoodIndex input target lo)
  =   makeIndices input target lo hi 
  ==. hi `C` N 
  ==. append (N) (C hi N)
  ==. append (makeIndices input target lo (hi-1)) (C hi N)
  *** QED 
  | not (isGoodIndex input target lo), isGoodIndex input target hi 
  =   makeIndices input target lo hi 
  ==. makeIndices input target (lo+1) hi
  ==. append (makeIndices input target (lo+1) (hi-1)) (C hi N)
       ? makeNewIndicesGoodLast input target (lo+1) hi  
  ==. append (makeIndices input target lo (hi-1)) (C hi N)
  *** QED 
  | isGoodIndex input target lo, isGoodIndex input target hi
  =   makeIndices input target lo hi 
  ==. lo `C` makeIndices input target (lo+1) hi
  ==. lo `C` (append (makeIndices input target (lo+1) (hi-1)) (C hi N))
       ? makeNewIndicesGoodLast input target (lo+1) hi  
  ==. (append (lo `C` makeIndices input target (lo+1) (hi-1)) (C hi N))
  ==. append (makeIndices input target lo (hi-1)) (C hi N)
  *** QED 

{-@ makeNewIndicesBadLast 
  :: input:SMTString -> target:SMTString -> lo:Nat -> hi:{Int | lo <= hi && (not (isGoodIndex input target hi))}
  -> {makeIndices input target lo hi == makeIndices input target lo (hi-1)}
  / [hi - lo]
@-}
-- NV sweet proof 
makeNewIndicesBadLast input target lo hi 
  | lo == hi, not (isGoodIndex input target lo)
  =   makeIndices input target lo (hi-1) 
  ==. N 
  ==. makeIndices input target lo hi
  *** QED 
  | not (isGoodIndex input target lo), not (isGoodIndex input target hi) 
  =   makeIndices input target lo hi 
  ==. makeIndices input target (lo+1) hi
  ==. makeIndices input target (lo+1) (hi-1)
       ? makeNewIndicesBadLast input target (lo+1) hi   
  ==. makeIndices input target lo (hi-1)
  *** QED 
  | isGoodIndex input target lo , not (isGoodIndex input target hi) 
  =   makeIndices input target lo hi 
  ==. lo `C` makeIndices input target (lo+1) hi
  ==. lo `C` makeIndices input target (lo+1) (hi-1)
       ? makeNewIndicesBadLast input target (lo+1) hi   
  ==. makeIndices input target lo (hi-1)
  *** QED 


catIndixes :: SMTString -> SMTString -> SMTString -> Int -> Int -> Proof 
{-@ catIndixes 
     :: input:SMTString -> x:SMTString 
     -> target:{SMTString | 0 <= stringLen input - stringLen target + 1} 
     -> lo:{Nat | lo <= stringLen input - stringLen target } 
     -> hi:{Int | stringLen input - stringLen target <= hi}
     -> { makeIndices input target lo hi == makeIndices (concatString input x) target lo (stringLen input - stringLen target) }
  @-}
catIndixes input x target lo hi 
  =   makeIndices input target lo hi
  ==. append (makeIndices input target lo (stringLen input - stringLen target))
                  (makeIndices input target (stringLen input - stringLen target + 1) hi)
       ? mergeIndixes input target lo (stringLen input - stringLen target) hi
  ==. append (makeIndices input target lo (stringLen input - stringLen target))
                  N
       ? maxIndixes input target (stringLen input - stringLen target + 1) hi
  ==. makeIndices input target lo (stringLen input - stringLen target)
       ? appendEmp (makeIndices input target lo (stringLen input - stringLen target))
  ==. makeIndices (concatString input x) target lo (stringLen input - stringLen target)
       ? concatmakeNewIndices lo (stringLen input - stringLen target) target input x 
  *** QED 




map_len_fusion :: SMTString -> SMTString -> List Int -> Proof
{-@ map_len_fusion 
  :: xi:SMTString 
  -> yi:SMTString 
  -> zis:List Int 
  -> {  map (shift (stringLen (concatString xi yi))) zis == map (shift (stringLen xi)) (map (shift (stringLen yi)) zis) 
     }
  @-}
map_len_fusion xi yi N 
  =   map (shift (stringLen (concatString xi yi))) N
  ==. N
  ==. map (shift (stringLen xi)) N
  ==. map (shift (stringLen xi)) (map (shift (stringLen yi)) N)
  *** QED  
map_len_fusion xi yi (C i is)
  =   map (shift (stringLen (concatString xi yi))) (C i is)
  ==. shift (stringLen (concatString xi yi)) i `C` map (shift (stringLen (concatString xi yi))) is 
  ==. shift (stringLen xi + stringLen yi) i `C` map (shift (stringLen (concatString xi yi))) is 
      ? concatLen xi yi 
  ==. shift (stringLen xi) (shift (stringLen yi) i) `C` map (shift (stringLen (concatString xi yi))) is 
      ? concatLen xi yi 
  ==. shift (stringLen xi) (shift (stringLen yi) i) `C` map (shift (stringLen xi)) (map (shift (stringLen yi)) is)
      ? map_len_fusion xi yi is 
  ==. map (shift (stringLen xi)) (shift (stringLen yi) i `C` map (shift (stringLen yi)) is)
  ==. map (shift (stringLen xi)) (map (shift (stringLen yi)) (i `C` is))
  *** QED 

smallInput :: SMTString -> SMTString -> Int -> Int -> Proof  
{-@ smallInput :: input:SMTString -> target:{SMTString | stringLen input < stringLen target } -> lo:Nat -> hi:Int 
           -> {makeIndices input target lo hi == N } 
           / [hi -lo]
  @-}
smallInput input target lo hi 
  | hi < lo 
  = makeIndices input target lo hi 
  ==. N
  *** QED  
  | lo == hi, not (isGoodIndex input target lo)
  = makeIndices input target lo hi 
  ==. N
  *** QED  
  | not (isGoodIndex input target lo)
  = makeIndices input target lo hi 
  ==. makeIndices input target (lo+1) hi
  ==. N ? smallInput input target (lo+1) hi 
  *** QED  



-------------------------------------------------------------------------------
----------  Indexing ----------------------------------------------------------
-------------------------------------------------------------------------------

   
data List a = N | C a (List a) deriving (Show, Eq)
{-@ data List [idxlen] a = N | C {idxhd :: a , idxtl :: List a} @-}


{-@ measure idxlen @-}
{-@ idxlen :: List a -> Nat @-} 
idxlen :: List a -> Int 
idxlen N = 0 
idxlen (C _ xs) = 1 + idxlen xs 

{-@ reflect map @-}
map :: (a -> b) -> List a -> List b
map _ N = N
map f (C x xs) = C (f x) (map f xs)

{-@ reflect append @-}
append :: List a -> List a -> List a 
append N xs = xs 
append (C x xs) ys = C x (append xs ys)

{-@ reflect shift @-}
shift :: Int -> Int -> Int 
shift x y = x + y 

{-@ symbolVal :: forall n proxy. KnownSymbol n => x:proxy n 
  -> {v:String | v == n && v == symbolVal x } @-}
{-@ measure symbolVal :: p n -> String @-}

{-@ reflect makeNewIndices @-}
{-@ makeNewIndices :: s1:SMTString -> s2:SMTString -> target:SMTString -> List (GoodIndex {concatString s1 s2} target) @-}
makeNewIndices :: SMTString -> SMTString -> SMTString -> List Int 
makeNewIndices s1 s2 target
  | stringLen target < 2 
  = N
  | otherwise
  = makeIndices (concatString s1 s2) target
                 (maxInt (stringLen s1 - (stringLen target-1)) 0)
                 (stringLen s1 - 1)


{-@ reflect maxInt @-}
maxInt :: Int -> Int -> Int 
maxInt x y = if x <= y then y else x 

{-@ reflect makeIndices @-}

makeIndices :: SMTString -> SMTString -> Int -> Int -> List Int 
{-@ makeIndices :: input:SMTString -> target:SMTString -> lo:{Int | 0 <= lo} -> hi:Int -> List (GoodIndex input target) 
  / [hi - lo] @-}
makeIndices input target lo hi 
  | hi < lo 
  = N
  | lo == hi, isGoodIndex input target lo
  = lo `C` N
  | lo == hi 
  = N
makeIndices input target lo hi 
  | isGoodIndex input target lo
  = lo `C` (makeIndices input target (lo + 1) hi)
  | otherwise 
  =    makeIndices input target (lo + 1) hi 

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

{-@ appendEmp :: xs:List a -> {append xs N = xs } @-} 
appendEmp :: List a -> Proof 
appendEmp N 
  =   append N N
  ==. N
  *** QED 
appendEmp (C x xs) 
  =   append (C x xs) N
  ==. C x (append xs N)
  ==. C x xs ? appendEmp xs 
  *** QED 


{-@ appendAssoc :: x:List a -> y:List a -> z:List a 
     -> {(append x (append y z)) == (append (append x y) z) } @-}
appendAssoc :: List a -> List a -> List a -> Proof
appendAssoc N y z 
  =   append N (append y z)
  ==. append y z
  ==. append (append N y) z
  *** QED 
appendAssoc (C x xs) y z
  =   append (C x xs) (append y z) 
  ==. C x (append xs (append y z))
  ==. C x (append (append xs y) z)
        ? appendAssoc xs y z
  ==. append (C x (append xs y)) z
  ==. append (append (C x xs) y) z
  *** QED 




makeNewIndicesNullRight :: SMTString -> SMTString -> Proof 
{-@ makeNewIndicesNullRight 
  :: s1:SMTString 
  -> t:SMTString 
  -> {makeNewIndices stringEmp s1 t == N } @-} 
makeNewIndicesNullRight s t 
  | stringLen t < 2 
  = makeNewIndices stringEmp s t  ==. N *** QED 
makeNewIndicesNullRight s t 
  =   makeNewIndices stringEmp s t
  ==. makeIndices (concatString stringEmp s) t
                   (maxInt (1 + stringLen stringEmp - stringLen t) 0)
                   (stringLen stringEmp - 1)
  ==. makeIndices s t
                   (maxInt (1 - stringLen t) 0)
                   (-1)
      ? concatStringNeutralRight s 
  ==. makeIndices s t 0 (-1)
  ==. N ? makeNewIndicesNullRightEmp s t  
  *** QED 


-- (x1 ~ x2) ~ (x3 ~ x4)
-- == 
-- ((x1 ~ (x2 ~ x3)) ~ x4)


appendGroupNew :: List a -> List a -> List a -> List a -> Proof
{-@ appendGroupNew 
  :: x1:List a 
  -> x2:List a 
  -> x3:List a 
  -> x4:List a 
  -> {   (append (append x1 x2) (append x3 x4))
      == (append (append x1 (append x2 x3)) x4)
     } @-}
appendGroupNew x1 x2 x3 x4 
  =   (append (append x1 x2) (append x3 x4))
  ==. (append (append (append x1 x2) x3) x4)
      ? appendAssoc (append x1 x2) x3 x4  
  ==. (append (append x1 (append x2 x3)) x4)
      ? appendAssoc x1 x2 x3
  *** QED 



-- (x1 ~ (x2 ~ x3)) ~ x4 == ((x1 ~ x2) ~ x3) ~ x4

appendUnGroupNew :: List a -> List a -> List a -> List a -> Proof
{-@ appendUnGroupNew 
  :: x1:List a 
  -> x2:List a 
  -> x3:List a 
  -> x4:List a 
  -> {   ((append (append (append x1 x2) x3) x4))
      == (append (append x1 (append x2 x3)) x4)
     } @-}
appendUnGroupNew x1 x2 x3 x4 
  =   append (append (append x1 x2) x3) x4
  ==. append (append x1 (append x2 x3)) x4
      ? appendAssoc x1 x2 x3 
  *** QED 


appendReorder :: List a -> List a -> List a -> List a -> List a -> Proof
{-@ appendReorder 
  :: x1:List a 
  -> x2:List a 
  -> x3:List a 
  -> x4:List a 
  -> x5:List a 
  -> {   (append (append x1 x2) (append (append x3 x4) x5))
      == (append (append (append (append x1 x2) x3) x4) x5)
     } @-}
appendReorder x1 x2 x3 x4 x5 
  =   append (append x1 x2) (append (append x3 x4) x5)
  ==. append (append x1 x2) (append x3 (append x4 x5))
       ? appendAssoc x3 x4 x5 
  ==. append (append (append x1 x2) x3) (append x4 x5)
      ? appendAssoc (append x1 x2) x3 (append x4 x5) 
  ==. append ((append (append (append x1 x2) x3)) x4) x5
      ? appendAssoc (append (append x1 x2) x3) x4 x5 
  *** QED 

-- ((x1~x2) ~ ((x3~x4) ~ x5))
-- == 
--   ((((x1~x2) ~x3) ~x4) ~x5

map_append :: (a -> b) -> List a -> List a -> Proof
{-@ map_append 
     :: f:(a -> b) -> xs:List a -> ys:List a 
     -> {map f (append xs ys) == append (map f xs) (map f ys)}
  @-}
map_append f N ys 
  =   map f (append N ys)
  ==. map f ys 
  ==. append N (map f ys)
  ==. append (map f N) (map f ys)
  *** QED 
map_append f (C x xs) ys 
  =   map f (append (C x xs) ys)
  ==. map f (x `C` (append xs ys))
  ==. f x `C` (map f (append xs ys))
  ==. f x `C` (append (map f xs) (map f ys))
      ? map_append f xs ys 
  ==. append (f x `C` map f xs) (map f ys)
  ==. append (map f (x `C` xs)) (map f ys)
  *** QED 

mapShiftZero :: List Int -> Proof
{-@ mapShiftZero :: is:List Int -> {map (shift 0) is == is } @-}
mapShiftZero N 
  = map (shift 0) N ==. N *** QED
mapShiftZero (C i is)
  =   map (shift 0) (C i is)
  ==. shift 0 i `C` map (shift 0) is 
  ==. i `C` is ? mapShiftZero is  
  *** QED 


{-@ makeNewIndicesNullRightEmp :: s:SMTString -> t:SMTString -> {makeIndices s t 0 (-1) == N } @-}
makeNewIndicesNullRightEmp :: SMTString -> SMTString -> Proof
makeNewIndicesNullRightEmp s t 
  =   makeIndices s t 0 (-1) 
  ==. N
  *** QED 

makeNewIndicesNullLeft :: SMTString -> SMTString -> Proof 
{-@ makeNewIndicesNullLeft 
  :: s:SMTString 
  -> t:SMTString 
  -> {makeNewIndices s stringEmp t == N } @-} 
makeNewIndicesNullLeft s t 
  | stringLen t < 2 
  = makeNewIndices s stringEmp t ==. N *** QED 
makeNewIndicesNullLeft  s t 
  | 1 + stringLen s <= stringLen t
  =   makeNewIndices s stringEmp t
  ==. makeIndices (concatString s stringEmp) t
                   (maxInt (1 + stringLen s - stringLen t)  0)
                   (stringLen s - 1)
  ==. makeIndices s t
                   0
                   (stringLen s - 1) 
                   ? concatStringNeutral s
  ==. makeIndices s t
                   0
                   (stringLen s - 1)
  ==. N ? makeNewIndicesNull1 s t 0 (stringLen s - 1)
  *** QED 
makeNewIndicesNullLeft s t 
  =   makeNewIndices s stringEmp t
  ==. makeIndices (concatString s stringEmp) t
                   (maxInt (1 + stringLen s - stringLen t)  0)
                   (stringLen s - 1)
  ==. makeIndices (concatString s stringEmp) t
                   (1 + stringLen s - stringLen t)
                   (stringLen s - 1)
  ==. makeIndices s t
                   (1 + stringLen s - stringLen t)
                   (stringLen s - 1) ? concatStringNeutral s 
  ==. N ? makeNewIndicesNull2 s t (1 + stringLen s - stringLen t) (stringLen s - 1)
  *** QED 


makeNewIndicesNull1 :: SMTString -> SMTString -> Int -> Int -> Proof 
{-@ makeNewIndicesNull1 
  :: s:SMTString 
  -> t:{SMTString | 1 + stringLen s <= stringLen t } 
  -> lo:Nat 
  -> hi:Int
  -> {makeIndices s t lo hi == N } / [hi - lo] @-} 
makeNewIndicesNull1 s1 t lo hi
  | hi < lo 
  = makeIndices s1 t lo hi ==. N *** QED 
  | lo == hi, not (isGoodIndex s1 t lo)
  = makeIndices s1 t lo hi ==. N *** QED  
  | not (isGoodIndex s1 t lo)
  =   makeIndices s1 t lo hi
  ==. makeIndices s1 t (lo + 1) hi 
  ==. N ? makeNewIndicesNull1 s1 t (lo+1) hi
  *** QED 


makeNewIndicesNull2 :: SMTString -> SMTString -> Int -> Int -> Proof 
{-@ makeNewIndicesNull2 
  :: s:SMTString 
  -> t:{SMTString | stringLen t < 2 + stringLen s } 
  -> lo:{Int | -1 <= lo && 1 + stringLen s - stringLen t <= lo  } 
  -> hi:{Int | lo <= hi}
  -> {makeIndices s t lo hi == N } / [hi - lo] @-} 
makeNewIndicesNull2 s1 t lo hi
  | lo == hi, not (isGoodIndex s1 t lo)
  = makeIndices s1 t lo hi ==. N *** QED  
  | not (isGoodIndex s1 t lo)
  =   makeIndices s1 t lo hi
  ==. makeIndices s1 t (lo + 1) hi 
  ==. N ? makeNewIndicesNull2 s1 t (lo+1) hi
  *** QED 
 
