{-
NV TODO 
1. refine data type
2. proove rest 1 monadic laws
-}



{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs               #-}


{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"     @-}
{- LIQUID "--stringtheory" @-}
{-@ LIQUID "--exactdc"      @-}

module StringIndexing where

import Language.Haskell.Liquid.String


import GHC.TypeLits
import Data.String hiding (fromString)

import Data.Proxy 


import Prelude hiding (mempty, mappend, id)
import Proves 



-- Structure that defines valid indeces of a type level target 
-- symbol in a value level string

data MI (tagret :: Symbol) s where 
  MI ::               SMTString        -- input string
                   -> (Idxes Int)      -- valid indeces of target in input
                   -> MI target s

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
  && (I + stringLen Target < stringLen Input)
  && (0 <= I)
  @-}


{-@ reflect mempty @-}
mempty :: forall (target :: Symbol). MI target SMTString
mempty = MI stringEmp IdxEmp

{-@ reflect mappend @-}
mappend :: forall (target :: Symbol).  (KnownSymbol target) => MI target SMTString -> MI target SMTString -> MI target SMTString
mappend (MI i1 is1) (MI i2 is2)
  = MI (concatString i1 i2)  
       (is1 `appendIdxes` mapIdxes (shift (stringLen i1)) is2
            `appendIdxes` makeIndexes i1 i2 (fromString (symbolVal (Proxy :: Proxy target))))

 



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
       (is1 `appendIdxes` IdxEmp) ? makeIndexesNullLeft i1 (fromString (symbolVal (Proxy :: Proxy target)))
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
       (IdxEmp `appendIdxes` mapIdxes (shift (stringLen stringEmp)) is
           `appendIdxes` makeIndexes stringEmp i (fromString (symbolVal (Proxy :: Proxy target))))
  ==. MI (concatString stringEmp i)  
       (mapIdxes (shift (stringLen stringEmp)) is
           `appendIdxes` makeIndexes stringEmp i (fromString (symbolVal (Proxy :: Proxy target))))
  ==. MI (concatString stringEmp i)  
       (mapIdxes (shift 0) is
           `appendIdxes` makeIndexes stringEmp i (fromString (symbolVal (Proxy :: Proxy target))))
  ==. MI (concatString stringEmp i)  
       (is `appendIdxes` makeIndexes stringEmp i (fromString (symbolVal (Proxy :: Proxy target))))
       ? mapShiftZero is 
  ==. MI (concatString stringEmp i)  
       (is `appendIdxes` IdxEmp) ? makeIndexesNullRight i (fromString (symbolVal (Proxy :: Proxy target)))
  ==. MI (concatString stringEmp i) is 
      ? appendIdxesEmp is
  ==. MI i is 
      ? concatStringNeutralRight i
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

-- String Library 


concatStringNeutral :: SMTString -> Proof
{-@ concatStringNeutral :: x:SMTString -> {concatString x stringEmp == x} @-}
concatStringNeutral = undefined


concatStringNeutralRight :: SMTString -> Proof
{-@ concatStringNeutralRight :: x:SMTString -> {concatString stringEmp x == x} @-}
concatStringNeutralRight = undefined


-------------------------------------------------------------------------------
----------  Indexing ----------------------------------------------------------
-------------------------------------------------------------------------------

   
data Idxes a = IdxEmp | Idxs a (Idxes a)
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
                 (maxInt (1 + stringLen s1 - stringLen target) (-1))
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
  && i + stringLen target < stringLen input
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
 
