{-

NV TODO 
1. refine data type
3. proove rest 2 monadic laws

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
       (is1 `appendIdxes` IdxEmp) ? makeIndexesNull i1 (fromString (symbolVal (Proxy :: Proxy target)))
  ==. MI (concatString i1 stringEmp) is1 
      ? appendIdxesEmp is1 
  ==. MI i1 is1 
      ? concatStringNeutral i1 
  *** QED 

-- String Library 


concatStringNeutral :: SMTString -> Proof
{-@ concatStringNeutral :: x:SMTString -> {concatString x stringEmp == x} @-}
concatStringNeutral = undefined



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
  | stringLen target == 0 
  = IdxEmp
  | otherwise
  = makeIndexes' (concatString s1 s2) target
                 (maxInt (1 + stringLen s1 - stringLen target) 0)
                 (stringLen s1 + stringLen target) 


{-@ reflect maxInt @-}
maxInt :: Int -> Int -> Int 
maxInt x y = if x <= y then y else x 

{-@ reflect makeIndexes' @-}

makeIndexes' :: SMTString -> SMTString -> Int -> Int -> Idxes Int 
{-@ makeIndexes' :: input:SMTString -> target:SMTString -> lo:Nat -> hi:{Nat | lo <= hi} -> Idxes (GoodIndex input target) / [hi - lo] @-}
makeIndexes' _ _ lo hi 
  | lo == hi = IdxEmp
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


makeIndexesNull :: SMTString -> SMTString -> Proof 
{-@ makeIndexesNull 
  :: s1:SMTString 
  -> t:SMTString 
  -> {makeIndexes s1 stringEmp t == IdxEmp } @-} 
makeIndexesNull s1 t 
  | stringLen t == 0 
  = makeIndexes s1 stringEmp t ==. IdxEmp *** QED 
makeIndexesNull s1 t 
  | 1 + stringLen s1 <= stringLen t
  =   makeIndexes s1 stringEmp t
  ==. makeIndexes' (concatString s1 stringEmp) t
                   (maxInt (1 + stringLen s1 - stringLen t) 0)
                   (stringLen s1 + stringLen t) 
  ==. makeIndexes' s1 t
                   0
                   (stringLen s1 + stringLen t) ? concatStringNeutral s1 
  ==. makeIndexes' s1 t
                   0
                   (stringLen s1 + stringLen t)
  ==. IdxEmp ? makeIndexesNull1 s1 t 0 (stringLen s1 + stringLen t)
  *** QED 
makeIndexesNull s1 t 
  =   makeIndexes s1 stringEmp t
  ==. makeIndexes' (concatString s1 stringEmp) t
                   (maxInt (1 + stringLen s1 - stringLen t) 0)
                   (stringLen s1 + stringLen t) 
  ==. makeIndexes' (concatString s1 stringEmp) t
                   (1 + stringLen s1 - stringLen t)
                   (stringLen s1 + stringLen t) 
  ==. makeIndexes' s1 t
                   (1 + stringLen s1 - stringLen t)
                   (stringLen s1 + stringLen t) ? concatStringNeutral s1 
  ==. IdxEmp ? makeIndexesNull2 s1 t (1 + stringLen s1 - stringLen t) (stringLen s1 + stringLen t)
  *** QED 


makeIndexesNull1 :: SMTString -> SMTString -> Int -> Int -> Proof 
{-@ makeIndexesNull1 
  :: s1:SMTString 
  -> t:{SMTString | 1 + stringLen s1 <= stringLen t } 
  -> lo:Nat 
  -> hi:{Nat | lo <= hi}
  -> {makeIndexes' s1 t lo hi == IdxEmp } / [hi - lo] @-} 
makeIndexesNull1 s1 t lo hi
  | lo == hi
  = makeIndexes' s1 t lo hi ==. IdxEmp *** QED  
  | not (isGoodIndex s1 t lo)
  =   makeIndexes' s1 t lo hi
  ==. makeIndexes' s1 t (lo + 1) hi 
  ==. IdxEmp ? makeIndexesNull1 s1 t (lo+1) hi
  *** QED 


makeIndexesNull2 :: SMTString -> SMTString -> Int -> Int -> Proof 
{-@ makeIndexesNull2 
  :: s1:SMTString 
  -> t:{SMTString | stringLen t < 1 + stringLen s1 } 
  -> lo:{Nat | 1 + stringLen s1 - stringLen t <= lo  } 
  -> hi:{Nat | lo <= hi}
  -> {makeIndexes' s1 t lo hi == IdxEmp } / [hi - lo] @-} 
makeIndexesNull2 s1 t lo hi
  | lo == hi
  = makeIndexes' s1 t lo hi ==. IdxEmp *** QED  
  | not (isGoodIndex s1 t lo)
  =   makeIndexes' s1 t lo hi
  ==. makeIndexes' s1 t (lo + 1) hi 
  ==. IdxEmp ? makeIndexesNull2 s1 t (lo+1) hi
  *** QED 
 
