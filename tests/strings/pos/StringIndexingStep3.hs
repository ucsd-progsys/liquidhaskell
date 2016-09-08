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


{-@ LIQUID "--higherorder"         @-}
{-@ LIQUID "--totality"            @-}
{-@ LIQUID "--exactdc"             @-}
{-@ LIQUID "--scrape-imports"      @-}
{-@ LIQUID "--scrape-used-imports" @-}

module Main where

import Language.Haskell.Liquid.String
import GHC.TypeLits
import Data.String hiding (fromString)
import Data.Proxy 
import Prelude hiding (mempty, mappend, id, mconcat)
import Language.Haskell.Liquid.ProofCombinators 

import Data.Maybe 

todo =  undefined

{-
-- Easy 
mergeIndixes
catIndixes
-}


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

test1   = indices input1 
input1  = fromString $ clone 100 "ababcabcab"


indices :: SMTString -> Idxes Int 
indices input 
  = case toMI input :: MI "abcab" SMTString  of 
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

toMIPar :: forall (target :: Symbol). (KnownSymbol target) => SMTString -> MI target SMTString 
toMIPar input = mconcatPar n2 (toMI <$> chunkString n1 input)
  where
    n1 = 2
    n2 = 2

toMI :: forall (target :: Symbol). (KnownSymbol target) => SMTString -> MI target SMTString 
toMI input = if isNullString input then mempty else  MI input (makeIndexes' input (fromString (symbolVal (Proxy :: Proxy target))) 0 (stringLen input - 1))

getIndex :: forall (target :: Symbol).  MI target SMTString -> Idxes Int 
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
     -> (Idxes Int)      -- valid indeces of target in input
     -> MI target s
  deriving (Show)

{-@ data MI target s 
  = MI { input :: SMTString
       , idxes :: Idxes Int 
       } @-}


{- data MI target s 
  = MI { input :: SMTString
       , idxes :: Idxes (GoodIndex input target)
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
mempty = MI stringEmp IdxEmp

{-@ reflect mappend @-}
mappend :: forall (target :: Symbol).  (KnownSymbol target) => MI target SMTString -> MI target SMTString -> MI target SMTString
mappend (MI i1 is1) (MI i2 is2)
  = MI (concatString i1 i2) -- (mappendMakeIndixes i1 i2 (fromString (symbolVal (Proxy :: Proxy target))) is1 is2)
    ((is1 
        `appendIdxes` 
      makeIndexes i1 i2 (fromString (symbolVal (Proxy :: Proxy target))))
        `appendIdxes` 
      mapIdxes (shift (stringLen i1)) is2)            
 

-------------------------------------------------------------------------------
--------------- PROOFS  -------------------------------------------------------
-------------------------------------------------------------------------------

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
        ? emptyIndexes y (assumeGoodIndex yi (fromString (symbolVal (Proxy :: Proxy target))) yis)
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
      ?emptyIndexes y (assumeGoodIndex yi (fromString (symbolVal (Proxy :: Proxy target))) yis)
  ==. mappend (MI (concatString xi yi)  
                  ( (xis `appendIdxes` makeIndexes xi yi (fromString (symbolVal (Proxy :: Proxy target))))
                         `appendIdxes` mapIdxes (shift (stringLen xi)) yis
                  )
              ) (MI zi zis)
  ==. mappend (mappend (MI xi xis) (MI yi yis)) (MI zi zis)
  *** QED 

-------------------------------------------------------------------------------
------------------ Helper Proofs ----------------------------------------------
-------------------------------------------------------------------------------


{-@ assumeGoodIndex :: input:SMTString -> target:SMTString -> is:Idxes Int 
                    -> {v:Idxes (GoodIndex input target) | v == is} @-} 
assumeGoodIndex :: SMTString -> SMTString -> Idxes Int -> Idxes Int 
assumeGoodIndex input target is 
  = if isJust (areGoodIndexes input target is) then fromJust (areGoodIndexes input target is) else error ""  


{-@ areGoodIndexes :: input:SMTString -> target:SMTString -> is:Idxes Int 
                   -> Maybe ({v:Idxes (GoodIndex input target) | v == is}) @-} 
areGoodIndexes :: SMTString -> SMTString -> Idxes Int -> Maybe (Idxes Int) 
areGoodIndexes input target IdxEmp
  = Just IdxEmp
areGoodIndexes input target (Idxs x xs)
  | isGoodIndex input target x 
  = case areGoodIndexes input target xs of 
       Nothing -> Nothing 
       Just is -> Just (Idxs x is) 
  | otherwise
  = Nothing 

  
emptyIndexes :: forall (target :: Symbol). (KnownSymbol target) => MI target SMTString -> Idxes Int  -> Proof
{-@ emptyIndexes :: mi:MI target SMTString
                 -> is:{Idxes (GoodIndex (inputMI mi) target) | is == indixesMI mi && stringLen (inputMI mi) < stringLen target}
                 -> { is == IdxEmp } @-}
emptyIndexes (MI _ _) IdxEmp 
  = trivial 
emptyIndexes (MI _ _) (Idxs _ _)
  = trivial 


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
                   (maxInt (stringLen xi - (stringLen tg-1)) 0)
                   (stringLen xi - 1)
  ==. makeIndexes' (concatString (concatString xi yi) zi) tg 
                   (maxInt (stringLen xi - (stringLen tg-1)) 0)
                   (stringLen xi - 1)
     ?concatStringAssoc xi yi zi 
  ==. makeIndexes' (concatString xi yi) tg 
                   (maxInt (stringLen xi - (stringLen tg-1)) 0)
                   (stringLen xi - 1)                
      ? concatMakeIndexes (maxInt (stringLen xi - (stringLen tg-1)) 0) (stringLen xi - 1) tg (concatString xi yi) zi 
  ==. makeIndexes xi yi tg 
  *** QED 



{-@ concatMakeIndexes
  :: lo:Nat -> hi:Int
  -> target: SMTString
  -> input : {SMTString | hi + stringLen target <= stringLen input } 
  -> input': SMTString   
  -> {  makeIndexes' (concatString input input') target lo hi == makeIndexes' input target lo hi }
  / [hi - lo]  @-}
concatMakeIndexes :: Int -> Int -> SMTString -> SMTString -> SMTString  -> Proof
concatMakeIndexes lo hi target input input'
  | hi < lo 
  =   makeIndexes' input target lo hi
  ==. IdxEmp
  ==. makeIndexes' (concatString input input') target lo hi 
  *** QED 
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
  -> { mapIdxes (shift (stringLen xi)) (makeIndexes yi zi tg) == makeIndexes (concatString xi yi) zi tg }
  @-}
shiftIndexesRight :: SMTString -> SMTString -> SMTString -> SMTString -> Proof
shiftIndexesRight xi yi zi tg
  | stringLen tg < 2 
  =   makeIndexes (concatString xi yi) zi tg 
  ==. IdxEmp
  ==. mapIdxes (shift (stringLen xi)) IdxEmp
  ==. mapIdxes (shift (stringLen xi)) (makeIndexes yi zi tg)
  *** QED 
shiftIndexesRight xi yi zi tg
-- NV NV NV 
-- This is suspicious!!! it should require exactly the precondition 
-- || tg || <= || yi || 
--   | stringLen tg  <= stringLen yi + 1 
  =   makeIndexes (concatString xi yi) zi tg  
  ==. makeIndexes' (concatString (concatString xi yi) zi) tg 
                   (maxInt (stringLen (concatString xi yi) - (stringLen tg -1)) 0)
                   (stringLen (concatString xi yi) - 1 )
  ==. makeIndexes' (concatString (concatString xi yi) zi) tg 
                   (stringLen (concatString xi yi) - (stringLen tg -1))
                   (stringLen (concatString xi yi) - 1 )
  ==. makeIndexes' (concatString (concatString xi yi) zi) tg 
                   (stringLen xi + stringLen yi - stringLen tg + 1)
                   (stringLen xi + stringLen yi - 1 )
  ==. makeIndexes' (concatString xi (concatString yi zi)) tg 
                   (stringLen xi + stringLen yi - stringLen tg + 1)
                   (stringLen xi + stringLen yi - 1 )
       ?concatStringAssoc xi yi zi
  ==. mapIdxes (shift (stringLen xi)) (makeIndexes' (concatString yi zi) tg (stringLen yi - stringLen tg + 1) (stringLen yi - 1))
       ? shiftIndexesRight' (stringLen yi - stringLen tg + 1)
                            (stringLen yi - 1)
                            xi 
                            (concatString yi zi)
                            tg 
  ==. mapIdxes (shift (stringLen xi)) 
               (makeIndexes' (concatString yi zi) tg 
                             (maxInt (stringLen yi - (stringLen tg -1)) 0)
                             (stringLen yi -1))
  ==. mapIdxes (shift (stringLen xi)) 
               (makeIndexes yi zi tg)
  *** QED

{-@ shiftIndexesRight'
  :: lo:Nat 
  -> hi:Int  
  -> x:SMTString 
  -> input:SMTString 
  -> tg:SMTString
  -> { mapIdxes (shift (stringLen x)) (makeIndexes' input tg lo hi) == makeIndexes' (concatString x input) tg (stringLen x + lo) (stringLen x + hi) }
  / [if hi < lo then 0 else  hi-lo]
  @-}
shiftIndexesRight' :: Int -> Int -> SMTString -> SMTString -> SMTString -> Proof
shiftIndexesRight' lo hi x input target
  | hi < lo 
  =   mapIdxes (shift (stringLen x)) (makeIndexes' input target lo hi)
  ==. mapIdxes (shift (stringLen x)) IdxEmp
  ==. IdxEmp
  ==. makeIndexes' (concatString x input) target (stringLen x + lo) (stringLen x + hi)
  *** QED 
  | lo == hi, isGoodIndex input target lo 
  =   mapIdxes (shift (stringLen x)) (makeIndexes' input target lo hi)
  ==. mapIdxes (shift (stringLen x)) (lo `Idxs` IdxEmp)
  ==. ((shift (stringLen x)) lo) `Idxs` (mapIdxes (shift (stringLen x)) IdxEmp)
  ==. (stringLen x + lo) `Idxs` IdxEmp
  ==. makeIndexes' (concatString x input) target (stringLen x + lo) (stringLen x + hi)
     ? isGoodIndexConcatFront input x target lo  -- ( => IsGoodIndex (concatString x input) target (stringLen x + lo))
  *** QED 
  | lo == hi
  =   mapIdxes (shift (stringLen x)) (makeIndexes' input target lo hi)
  ==. mapIdxes (shift (stringLen x)) IdxEmp
  ==. IdxEmp
  ==. makeIndexes' (concatString x input) target (stringLen x + lo) (stringLen x + hi)
     ? (isGoodIndexConcatFront input x target lo *** QED)
  *** QED 

shiftIndexesRight' lo hi x input target
  | isGoodIndex input target lo
  =   mapIdxes (shift (stringLen x)) (makeIndexes' input target lo hi)
  ==. mapIdxes (shift (stringLen x)) (lo `Idxs`(makeIndexes' input target (lo+1) hi))
  ==. (shift (stringLen x) lo) `Idxs` (mapIdxes (shift (stringLen x)) (makeIndexes' input target (lo+1) hi))
  ==. (shift (stringLen x) lo) `Idxs` (makeIndexes' (concatString x input) target (stringLen x + (lo+1)) (stringLen x + hi))
      ? shiftIndexesRight' (lo+1) hi x input target
  ==. (stringLen x + lo) `Idxs` (makeIndexes' (concatString x input) target (stringLen x + (lo+1)) (stringLen x + hi))
  ==. makeIndexes' (concatString x input) target (stringLen x + lo) (stringLen x + hi)
     ? (isGoodIndexConcatFront input x target lo *** QED)
  *** QED 
  | otherwise
  =   mapIdxes (shift (stringLen x)) (makeIndexes' input target lo hi)
  ==. mapIdxes (shift (stringLen x)) (makeIndexes' input target (lo + 1) hi)
  ==. makeIndexes' (concatString x input) target (stringLen x + (lo+1)) (stringLen x + hi)
      ? shiftIndexesRight' (lo+1) hi x input target
  ==. makeIndexes' (concatString x input) target (stringLen x + lo) (stringLen x + hi)
     ? (isGoodIndexConcatFront input x target lo *** QED)
  *** QED 


{-@ shiftNewIndexes
  :: xi:SMTString 
  -> yi:SMTString 
  -> zi:SMTString 
  -> tg:{SMTString | stringLen yi < stringLen tg  } 
  -> {  appendIdxes (makeIndexes xi (concatString yi zi) tg) (mapIdxes (shift (stringLen xi)) (makeIndexes yi zi tg)) == appendIdxes (makeIndexes xi yi tg) (makeIndexes (concatString xi yi) zi tg)
     }
  @-}
shiftNewIndexes :: SMTString -> SMTString -> SMTString -> SMTString -> Proof
shiftNewIndexes xi yi zi tg 
  | stringLen tg < 2 
  =   appendIdxes (makeIndexes xi (concatString yi zi) tg) (mapIdxes (shift (stringLen xi)) (makeIndexes yi zi tg)) 
  ==. appendIdxes IdxEmp (mapIdxes (shift (stringLen xi)) IdxEmp) 
  ==. mapIdxes (shift (stringLen xi)) IdxEmp 
  ==. IdxEmp 
  ==. appendIdxes IdxEmp IdxEmp
  ==. appendIdxes (makeIndexes xi yi tg) (makeIndexes (concatString xi yi) zi tg)
  *** QED 

shiftNewIndexes xi yi zi tg 
-- THIS ALWAYS HOLDS 
--   | stringLen yi + 1 <= stringLen tg
  | 0 <= stringLen xi + stringLen yi - stringLen tg + 1
  = let minidx = maxInt (stringLen xi - stringLen tg + 1) 0 in 
      appendIdxes (makeIndexes xi (concatString yi zi) tg) 
                  (mapIdxes (shift (stringLen xi)) (makeIndexes yi zi tg)) 
  ==. appendIdxes (makeIndexes' (concatString xi (concatString yi zi)) tg
                                (maxInt (stringLen xi - stringLen tg + 1) 0)
                                (stringLen xi -1)) 
                  (mapIdxes (shift (stringLen xi)) 
                            (makeIndexes' (concatString yi zi) tg
                                          (maxInt (stringLen yi - stringLen tg +1) 0)
                                          (stringLen yi -1)
                            )) 
  ==. appendIdxes (makeIndexes' (concatString xi (concatString yi zi)) tg
                                minidx
                                (stringLen xi -1)) 
                  (mapIdxes (shift (stringLen xi)) 
                            (makeIndexes' (concatString yi zi) tg
                                           0
                                          (stringLen yi -1)
                            )) 
  ==. appendIdxes (makeIndexes' (concatString xi (concatString yi zi)) tg
                                minidx
                                (stringLen xi -1)) 
                  (makeIndexes' (concatString xi (concatString yi zi)) tg 
                                (stringLen xi) 
                                (stringLen xi + stringLen yi -1)) 
      ? shiftIndexesRight' 0 (stringLen yi -1) xi (concatString yi zi) tg 
  ==. appendIdxes (makeIndexes' (concatString (concatString xi yi) zi) tg
                                minidx
                                (stringLen xi -1)) 
                  (makeIndexes' (concatString (concatString xi yi) zi) tg 
                                (stringLen xi) 
                                (stringLen xi + stringLen yi -1)) 
      ? concatStringAssoc xi yi zi 

  ==. appendIdxes (appendIdxes 

                  (makeIndexes' (concatString (concatString xi yi) zi) tg
                                minidx
                                (stringLen xi + stringLen yi - stringLen tg))

                  (makeIndexes' (concatString (concatString xi yi) zi) tg
                                (stringLen xi + stringLen yi - stringLen tg + 1)
                                (stringLen xi -1))

                                ) 
                  (makeIndexes' (concatString (concatString xi yi) zi) tg 
                                (stringLen xi)
                                (stringLen xi + stringLen yi -1)) 
      ? mergeIndixes (concatString (concatString xi yi) zi) tg 
                     minidx
                     (stringLen xi + stringLen yi - stringLen tg)
                     (stringLen xi -1)


  ==. appendIdxes (makeIndexes' (concatString (concatString xi yi) zi) tg
                                minidx
                                (stringLen xi + stringLen yi - stringLen tg))

                 (appendIdxes

                  (makeIndexes' (concatString (concatString xi yi) zi) tg
                                (stringLen xi + stringLen yi - stringLen tg +1)
                                (stringLen xi -1))

                                
                  (makeIndexes' (concatString (concatString xi yi) zi) tg 
                                (stringLen xi)
                                (stringLen xi + stringLen yi -1)) )
      ? appendIdxesAssoc
              (makeIndexes' (concatString (concatString xi yi) zi) tg
                                minidx
                                (stringLen xi + stringLen yi - stringLen tg))
              (makeIndexes' (concatString (concatString xi yi) zi) tg
                                (stringLen xi + stringLen yi - stringLen tg+1)
                                (stringLen xi -1))
              (makeIndexes' (concatString (concatString xi yi) zi) tg 
                                (stringLen xi)
                                (stringLen xi + stringLen yi -1))

  ==. appendIdxes (makeIndexes' (concatString (concatString xi yi) zi) tg
                                minidx
                                (stringLen xi + stringLen yi - stringLen tg))

                  (makeIndexes' (concatString (concatString xi yi) zi) tg
                                ((stringLen xi + stringLen yi - stringLen tg+1))
                                (stringLen xi + stringLen yi -1))
     ? mergeIndixes (concatString (concatString xi yi) zi) tg 
                  ((stringLen xi + stringLen yi - stringLen tg+1))
                  (stringLen xi -1)
                  (stringLen xi + stringLen yi -1)

  ==. appendIdxes (makeIndexes' (concatString (concatString xi yi) zi) tg
                                minidx 
                                (stringLen (concatString xi yi)  - stringLen tg))

                  (makeIndexes' (concatString (concatString xi yi) zi) tg
                                (stringLen xi + stringLen yi - stringLen tg + 1)
                                (stringLen xi + stringLen yi -1))

  ==. appendIdxes (makeIndexes' (concatString xi yi) tg 
                                minidx
                                (stringLen xi-1)
                  ) 
                  (makeIndexes' (concatString (concatString xi yi) zi) tg
                                (stringLen xi + stringLen yi - stringLen tg + 1)
                                (stringLen xi + stringLen yi  - 1)
                  )
      ? catIndixes (concatString xi yi) zi tg minidx (stringLen xi-1)

  ==. appendIdxes (makeIndexes' (concatString xi yi) tg 
                                minidx
                                (stringLen xi-1)
                  ) 
                  (makeIndexes' (concatString (concatString xi yi) zi) tg
                                (maxInt (stringLen xi + stringLen yi - stringLen tg + 1) 0)
                                (stringLen xi + stringLen yi  - 1)
                  )

  ==. appendIdxes (makeIndexes' (concatString xi yi) tg 
                                minidx
                                (stringLen xi-1)
                  ) 
                  (makeIndexes' (concatString (concatString xi yi) zi) tg
                                (maxInt (stringLen (concatString xi yi) - stringLen tg + 1) 0)
                                (stringLen (concatString xi yi) - 1)
                  )
  ==. appendIdxes (makeIndexes' (concatString xi yi) tg 
                                (maxInt (stringLen xi - stringLen tg +1) 0)
                                (stringLen xi-1)
                  ) 
                  (makeIndexes' (concatString (concatString xi yi) zi) tg
                                (maxInt (stringLen (concatString xi yi) - stringLen tg + 1) 0)
                                (stringLen (concatString xi yi) - 1)
                  )
  ==. appendIdxes (makeIndexes xi yi tg) (makeIndexes (concatString xi yi) zi tg)
  *** QED 

--   | stringLen yi + 1 <= stringLen tg
  | stringLen xi + stringLen yi  + 1 <= stringLen tg
  =   appendIdxes (makeIndexes xi (concatString yi zi) tg) 
                  (mapIdxes (shift (stringLen xi)) (makeIndexes yi zi tg)) 
  ==. appendIdxes (makeIndexes' (concatString xi (concatString yi zi)) tg
                                (maxInt (stringLen xi - stringLen tg + 1) 0)
                                (stringLen xi -1)) 
                  (mapIdxes (shift (stringLen xi)) 
                            (makeIndexes' (concatString yi zi) tg
                                          (maxInt (stringLen yi - stringLen tg +1) 0)
                                          (stringLen yi -1)
                            )) 
  ==. appendIdxes (makeIndexes' (concatString xi (concatString yi zi)) tg
                                0
                                (stringLen xi -1)) 
                  (mapIdxes (shift (stringLen xi)) 
                            (makeIndexes' (concatString yi zi) tg
                                           0
                                          (stringLen yi -1)
                            )) 
  ==. appendIdxes (makeIndexes' (concatString xi (concatString yi zi)) tg
                                0
                                (stringLen xi -1)) 
                  (makeIndexes' (concatString xi (concatString yi zi)) tg 
                                (stringLen xi) 
                                (stringLen xi + stringLen yi -1)) 
      ? shiftIndexesRight' 0 (stringLen yi -1) xi (concatString yi zi) tg 
  ==. appendIdxes (makeIndexes' (concatString (concatString xi yi) zi) tg
                                0
                                (stringLen xi -1)) 
                  (makeIndexes' (concatString (concatString xi yi) zi) tg 
                                (stringLen xi) 
                                (stringLen xi + stringLen yi -1)) 
      ? concatStringAssoc xi yi zi 

  ==. makeIndexes' (concatString (concatString xi yi) zi) tg
                                0
                                (stringLen (concatString xi yi) - 1)
  ==. makeIndexes' (concatString (concatString xi yi) zi) tg
                                0
                                (stringLen (concatString xi yi) - 1)
      ?mergeIndixes (concatString (concatString xi yi) zi) tg 0 (stringLen xi -1) (stringLen (concatString xi yi) -1)

  ==. appendIdxes IdxEmp 
                  (makeIndexes' (concatString (concatString xi yi) zi) tg
                                0
                                (stringLen (concatString xi yi) - 1)
                  )

  ==. appendIdxes (makeIndexes' (concatString xi yi) tg 
                                0
                                (stringLen xi-1)
                  ) 
                  (makeIndexes' (concatString (concatString xi yi) zi) tg
                                0
                                (stringLen (concatString xi yi) - 1)
                  )
      ? smallInput (concatString xi yi) tg 0 (stringLen xi -1)
  ==. appendIdxes (makeIndexes' (concatString xi yi) tg 
                                (maxInt (stringLen xi - stringLen tg +1) 0)
                                (stringLen xi-1)
                  ) 
                  (makeIndexes' (concatString (concatString xi yi) zi) tg
                                (maxInt (stringLen (concatString xi yi) - stringLen tg + 1) 0)
                                (stringLen (concatString xi yi) - 1)
                  )
  ==. appendIdxes (makeIndexes xi yi tg) (makeIndexes (concatString xi yi) zi tg)
  *** QED 

mergeIndixes :: SMTString -> SMTString -> Int -> Int -> Int -> Proof
{-@ mergeIndixes 
  :: input:SMTString -> target:SMTString -> lo:Nat -> mid:{Int | lo <= mid + 1} -> hi:{Int | mid <= hi} 
  -> {makeIndexes' input target lo hi == appendIdxes (makeIndexes' input target lo mid) (makeIndexes' input target (mid+1) hi)} @-}
mergeIndixes = todo 


catIndixes :: SMTString -> SMTString -> SMTString -> Int -> Int -> Proof 
{-@ catIndixes 
     :: input:SMTString -> x:SMTString -> target :SMTString -> lo:Nat -> hi:Int
    -> { makeIndexes' input target lo hi == makeIndexes' (concatString input x) target lo (stringLen input - stringLen target) }
  @-}
catIndixes = todo 

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

smallInput :: SMTString -> SMTString -> Int -> Int -> Proof  
{-@ smallInput :: input:SMTString -> target:{SMTString | stringLen input < stringLen target } -> lo:Nat -> hi:Int 
           -> {makeIndexes' input target lo hi == IdxEmp } 
           / [hi -lo]
  @-}
smallInput input target lo hi 
  | hi < lo 
  = makeIndexes' input target lo hi 
  ==. IdxEmp
  *** QED  
  | lo == hi, not (isGoodIndex input target lo)
  = makeIndexes' input target lo hi 
  ==. IdxEmp
  *** QED  
  | not (isGoodIndex input target lo)
  = makeIndexes' input target lo hi 
  ==. makeIndexes' input target (lo+1) hi
  ==. IdxEmp ? smallInput input target (lo+1) hi 
  *** QED  



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
{-@ makeIndexes :: s1:SMTString -> s2:SMTString -> target:SMTString -> Idxes (GoodIndex {concatString s1 s2} target) @-}
makeIndexes :: SMTString -> SMTString -> SMTString -> Idxes Int 
makeIndexes s1 s2 target
  | stringLen target < 2 
  = IdxEmp
  | otherwise
  = makeIndexes' (concatString s1 s2) target
                 (maxInt (stringLen s1 - (stringLen target-1)) 0)
                 (stringLen s1 - 1)


{-@ reflect maxInt @-}
maxInt :: Int -> Int -> Int 
maxInt x y = if x <= y then y else x 

{-@ reflect makeIndexes' @-}

makeIndexes' :: SMTString -> SMTString -> Int -> Int -> Idxes Int 
{-@ makeIndexes' :: input:SMTString -> target:SMTString -> lo:{Int | 0 <= lo} -> hi:Int -> Idxes (GoodIndex input target) 
  / [hi - lo] @-}
makeIndexes' input target lo hi 
  | hi < lo 
  = IdxEmp
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


{-@ appendIdxesAssoc :: x:Idxes a -> y:Idxes a -> z:Idxes a 
     -> {(appendIdxes x (appendIdxes y z)) == (appendIdxes (appendIdxes x y) z) } @-}
appendIdxesAssoc :: Idxes a -> Idxes a -> Idxes a -> Proof
appendIdxesAssoc IdxEmp y z 
  =   appendIdxes IdxEmp (appendIdxes y z)
  ==. appendIdxes y z
  ==. appendIdxes (appendIdxes IdxEmp y) z
  *** QED 
appendIdxesAssoc (Idxs x xs) y z
  =   appendIdxes (Idxs x xs) (appendIdxes y z) 
  ==. Idxs x (appendIdxes xs (appendIdxes y z))
  ==. Idxs x (appendIdxes (appendIdxes xs y) z)
        ? appendIdxesAssoc xs y z
  ==. appendIdxes (Idxs x (appendIdxes xs y)) z
  ==. appendIdxes (appendIdxes (Idxs x xs) y) z
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
                   (maxInt (1 + stringLen stringEmp - stringLen t) 0)
                   (stringLen stringEmp - 1)
  ==. makeIndexes' s t
                   (maxInt (1 - stringLen t) 0)
                   (-1)
      ? concatStringNeutralRight s 
  ==. makeIndexes' s t 0 (-1)
  ==. IdxEmp ? makeIndexesNullRightEmp s t  
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
appendGroupNew x1 x2 x3 x4 
  =   (appendIdxes (appendIdxes x1 x2) (appendIdxes x3 x4))
  ==. (appendIdxes (appendIdxes (appendIdxes x1 x2) x3) x4)
      ? appendIdxesAssoc (appendIdxes x1 x2) x3 x4  
  ==. (appendIdxes (appendIdxes x1 (appendIdxes x2 x3)) x4)
      ? appendIdxesAssoc x1 x2 x3
  *** QED 



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
appendUnGroupNew x1 x2 x3 x4 
  =   appendIdxes (appendIdxes (appendIdxes x1 x2) x3) x4
  ==. appendIdxes (appendIdxes x1 (appendIdxes x2 x3)) x4
      ? appendIdxesAssoc x1 x2 x3 
  *** QED 


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
appendReorder x1 x2 x3 x4 x5 
  =   appendIdxes (appendIdxes x1 x2) (appendIdxes (appendIdxes x3 x4) x5)
  ==. appendIdxes (appendIdxes x1 x2) (appendIdxes x3 (appendIdxes x4 x5))
       ? appendIdxesAssoc x3 x4 x5 
  ==. appendIdxes (appendIdxes (appendIdxes x1 x2) x3) (appendIdxes x4 x5)
      ? appendIdxesAssoc (appendIdxes x1 x2) x3 (appendIdxes x4 x5) 
  ==. appendIdxes ((appendIdxes (appendIdxes (appendIdxes x1 x2) x3)) x4) x5
      ? appendIdxesAssoc (appendIdxes (appendIdxes x1 x2) x3) x4 x5 
  *** QED 

-- ((x1~x2) ~ ((x3~x4) ~ x5))
-- == 
--   ((((x1~x2) ~x3) ~x4) ~x5

map_append :: (a -> b) -> Idxes a -> Idxes a -> Proof
{-@ map_append 
     :: f:(a -> b) -> xs:Idxes a -> ys:Idxes a 
     -> {mapIdxes f (appendIdxes xs ys) == appendIdxes (mapIdxes f xs) (mapIdxes f ys)}
  @-}
map_append f IdxEmp ys 
  =   mapIdxes f (appendIdxes IdxEmp ys)
  ==. mapIdxes f ys 
  ==. appendIdxes IdxEmp (mapIdxes f ys)
  ==. appendIdxes (mapIdxes f IdxEmp) (mapIdxes f ys)
  *** QED 
map_append f (Idxs x xs) ys 
  =   mapIdxes f (appendIdxes (Idxs x xs) ys)
  ==. mapIdxes f (x `Idxs` (appendIdxes xs ys))
  ==. f x `Idxs` (mapIdxes f (appendIdxes xs ys))
  ==. f x `Idxs` (appendIdxes (mapIdxes f xs) (mapIdxes f ys))
      ? map_append f xs ys 
  ==. appendIdxes (f x `Idxs` mapIdxes f xs) (mapIdxes f ys)
  ==. appendIdxes (mapIdxes f (x `Idxs` xs)) (mapIdxes f ys)
  *** QED 

mapShiftZero :: Idxes Int -> Proof
{-@ mapShiftZero :: is:Idxes Int -> {mapIdxes (shift 0) is == is } @-}
mapShiftZero IdxEmp 
  = mapIdxes (shift 0) IdxEmp ==. IdxEmp *** QED
mapShiftZero (Idxs i is)
  =   mapIdxes (shift 0) (Idxs i is)
  ==. shift 0 i `Idxs` mapIdxes (shift 0) is 
  ==. i `Idxs` is ? mapShiftZero is  
  *** QED 


{-@ makeIndexesNullRightEmp :: s:SMTString -> t:SMTString -> {makeIndexes' s t 0 (-1) == IdxEmp } @-}
makeIndexesNullRightEmp :: SMTString -> SMTString -> Proof
makeIndexesNullRightEmp s t 
  =   makeIndexes' s t 0 (-1) 
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
  | 1 + stringLen s <= stringLen t
  =   makeIndexes s stringEmp t
  ==. makeIndexes' (concatString s stringEmp) t
                   (maxInt (1 + stringLen s - stringLen t)  0)
                   (stringLen s - 1)
  ==. makeIndexes' s t
                   0
                   (stringLen s - 1) 
                   ? concatStringNeutral s
  ==. makeIndexes' s t
                   0
                   (stringLen s - 1)
  ==. IdxEmp ? makeIndexesNull1 s t 0 (stringLen s - 1)
  *** QED 
makeIndexesNullLeft s t 
  =   makeIndexes s stringEmp t
  ==. makeIndexes' (concatString s stringEmp) t
                   (maxInt (1 + stringLen s - stringLen t)  0)
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
  -> t:{SMTString | 1 + stringLen s <= stringLen t } 
  -> lo:Nat 
  -> hi:Int
  -> {makeIndexes' s t lo hi == IdxEmp } / [hi - lo] @-} 
makeIndexesNull1 s1 t lo hi
  | hi < lo 
  = makeIndexes' s1 t lo hi ==. IdxEmp *** QED 
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
 
