{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs               #-}


{-@ LIQUID "--higherorder"         @-}
{-@ LIQUID "--totality"            @-}
{-@ LIQUID "--exactdc"             @-}

module StringIndexing where


import Language.Haskell.Liquid.String
import GHC.TypeLits
import Data.String hiding (fromString)
import Prelude hiding ( mempty, mappend, id, mconcat, map 
                      , error, undefined 
                      )
import Language.Haskell.Liquid.ProofCombinators 

import Data.Maybe 

import Data.Proxy 
{-@ symbolVal :: forall n proxy. KnownSymbol n => x:proxy n 
  -> {v:String | v == n && v == symbolVal x } @-}
{-@ measure symbolVal :: p n -> String @-}

-------------------------------------------------------------------------------
------------ | Interface ------------------------------------------------------
-------------------------------------------------------------------------------

main :: IO ()
main = 
  do input     <- fromString <$> readFile "input.txt"
     let mi1    = toMI input :: MI "abcab" 
     let is1    = indicesMI mi1 
     putStrLn   $ "Serial   Indices: " ++ show is1
     let mi2    = toMIPar 10 input :: MI "abcab" 
     let is2    = indicesMI mi2 
     putStrLn   $ "Parallel Indices: " ++ show is2
     putStrLn   $ "Are equal? " ++ show (is1 == is2)

test = indicesMI (toMI (fromString $ clone 100 "ababcabcab")  :: MI "abcab" )
  where
    clone i xs = concat (replicate i xs) 



toMI   :: forall (target :: Symbol). (KnownSymbol target) => SMTString -> MI target 
toMI input  
  | isNullString input = mempty
  | otherwise          = MI input (makeIndices input (fromString (symbolVal (Proxy :: Proxy target))) 0 (stringLen input - 1))

toMIPar :: forall (target :: Symbol). (KnownSymbol target) => Int -> SMTString -> MI target  
toMIPar chunksize input 
  = mconcat (map toMI (chunk chunksize input))

-------------------------------------------------------------------------------
----------  Indexing Structure Definition -------------------------------------
-------------------------------------------------------------------------------

data MI (target :: Symbol) where 
  MI :: SMTString       -- | input string
     -> (List Int)      -- | valid indices of target in input
     -> MI target
  deriving (Show)

{-@ data MI target 
  = MI { input   :: SMTString
       , indices :: List (GoodIndex input target)
       } @-}

{-@ type GoodIndex Input Target 
  = {i:Int | IsGoodIndex Input Target i }
  @-}

{-@ predicate IsGoodIndex Input Target I
  =  (subString Input I (stringLen Target)  == Target)
  && (I + stringLen Target <= stringLen Input)
  && (0 <= I)
  @-}

{-@ measure indicesMI @-}
indicesMI (MI _ is) = is 

{-@ measure inputMI @-}
inputMI (MI i _) = i 

-------------------------------------------------------------------------------
----------  Monoid Operators on MI --------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect mempty @-}
mempty :: forall (target :: Symbol). (KnownSymbol target) =>  MI target
mempty = MI stringEmp N

{-@ reflect mconcat @-}
mconcat :: forall (target :: Symbol). (KnownSymbol target) => List (MI target) -> MI target 
mconcat N        = mempty
mconcat (C x xs) = mappend x (mconcat xs)

{-@ reflect mappend @-}
mappend :: forall (target :: Symbol).  (KnownSymbol target) => MI target -> MI target -> MI target
mappend (MI i1 is1) (MI i2 is2)
  = MI (concatString i1 i2)
       ((castGoodIndexRightList (fromString (symbolVal (Proxy :: Proxy target))) i1 i2 is1
          `append`
        makeNewIndices i1 i2 (fromString (symbolVal (Proxy :: Proxy target)))
       ) `append`
       (map (shiftStringRight (fromString (symbolVal (Proxy :: Proxy target))) i1 i2) is2)) 

-- | Helpers 
{-@ reflect shiftStringRight @-}
shiftStringRight :: SMTString -> SMTString -> SMTString -> Int -> Int 
{-@ shiftStringRight :: target:SMTString -> left:SMTString -> right:SMTString -> i:GoodIndex right target 
  -> {v:(GoodIndex {concatString left right} target) | v == i + stringLen left } @-}
shiftStringRight target left right i 
  = cast (subStringConcatFront right left (stringLen target) i) (shift (stringLen left) i)

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

{-@ reflect shift @-}
shift :: Int -> Int -> Int 
shift x y = x + y 

-- | Casting good indices: the below operators are liquid casts and behave like id at runtime

-- NV: The recursion is required as there is no other way to (access &) cast _each_ element of the input list
{-@ reflect castGoodIndexRightList @-}
castGoodIndexRightList :: SMTString -> SMTString -> SMTString -> List Int -> List Int    
{-@ castGoodIndexRightList :: target:SMTString -> input:SMTString -> x:SMTString -> is:List (GoodIndex input target) 
    -> {v:List (GoodIndex {concatString input x} target) | v == is} @-}
castGoodIndexRightList target input x N 
  = N 
castGoodIndexRightList target input x (C i is) 
  = C (castGoodIndexRight target input x i) (castGoodIndexRightList target input x is)  

{-@ reflect castGoodIndexRight @-}
castGoodIndexRight :: SMTString -> SMTString -> SMTString -> Int -> Int  
{-@ castGoodIndexRight :: target:SMTString -> input:SMTString -> x:SMTString -> i:GoodIndex input target 
   -> {v:(GoodIndex {concatString input x} target)| v == i} @-}
castGoodIndexRight target input x i  = cast (subStringConcat input x (stringLen target) i) i

-------------------------------------------------------------------------------
----------  Indices' Generation -----------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect makeIndices @-}
makeIndices :: SMTString -> SMTString -> Int -> Int -> List Int 
{-@ makeIndices :: input:SMTString -> target:SMTString -> lo:Nat -> hi:Int -> List (GoodIndex input target) 
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
----------  List Structure ----------------------------------------------------
-------------------------------------------------------------------------------
   
data List a = N | C a (List a) deriving (Show, Eq)
{-@ data List [llen] a 
  = N | C {lhead :: a , ltail :: List a} @-}


{-@ measure llen @-}
{-@ llen :: List a -> Nat @-} 
llen :: List a -> Int 
llen N        = 0 
llen (C _ xs) = 1 + llen xs 

{-@ reflect map @-}
map :: (a -> b) -> List a -> List b
map _ N        = N
map f (C x xs) = C (f x) (map f xs)

{-@ reflect append @-}
append :: List a -> List a -> List a 
append N        ys = ys 
append (C x xs) ys = x `C` (append xs ys)

-------------------------------------------------------------------------------
----------  String Chunking ---------------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect chunk @-}
{-@ chunk :: Int -> xs:SMTString -> List (SMTString) / [stringLen xs] @-}
chunk :: Int -> SMTString -> List (SMTString)
chunk i xs 
  | i <= 0 
  = C xs N 
  | stringLen xs <= i 
  = C xs N 
  | otherwise
  = C (takeString i xs) (chunk i (takeString i xs))


