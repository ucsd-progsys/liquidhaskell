{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs               #-}


{-@ LIQUID "--totality"          @-}
{-@ LIQUID "--stringtheory"      @-}

module StringIndexing where


import GHC.TypeLits
import Data.String 

import Data.Proxy 
-- Structure that defines valid indeces of a type level target 
-- symbol in a value level string

data MI (tagret :: Symbol) s where 
  MI :: IsString s => s        -- input string
                   -> [Int]    -- valid indeces of target in input
                   -> MI target s

{-@ MI :: input:s 
       -> [GoodIndex input target]
       -> MI s @-}


{-@ type GoodIndex Input Target 
  = {i:Int |  IsGoodIndex Input Target i}
  @-}

{-@ predicate IsGoodIndex Input Target I
  =  (subString Input I (stringLen Target)  == Target)
  && (I + stringLen Target < stringLen Input)
  && (0 <= I)
  @-}

{-@ measure stringLen    :: String -> Int @-}
{-@ measure subString    :: String -> Int -> Int -> String @-}
{-@ measure concatString :: String -> String -> String @-}

mempty :: forall (target :: Symbol). MI target String
mempty = MI "" []


mappend :: forall (target :: Symbol). (KnownSymbol target) => MI target String -> MI target String -> MI target String
mappend (MI i1 is1) (MI i2 is2)
  = MI input (is ++ is1 ++ map ((length i1) +) is2)
  where 
    is     = filterIndex input target [(len1 - len) .. (len1 + len)]
    input  = i1 `concatString` i2 
    len1   = length i1 
    len    = length target 
    target = symbolVal (Proxy :: Proxy target)


{-@ symbolVal :: forall n proxy. KnownSymbol n => proxy n -> {v:String | v == n} @-}

filterIndex :: String -> String -> [Int] -> [Int]
{-@ filterIndex :: input:String -> target:String -> is:[Int] -> [GoodIndex input target] / [len is] @-}
filterIndex _ _ [] = []
filterIndex input target (i:is)
  | isGoodIndex input target i
  = i:filterIndex input target is 
  | otherwise 
  =   filterIndex input target is 


isGoodIndex :: String -> String -> Int -> Bool 
{-@ isGoodIndex :: input:String -> target:String -> i:Int 
  -> {b:Bool | Prop b <=> IsGoodIndex input target i} @-}
isGoodIndex input target i 
  =  subString input i (stringLen target)  == target  
  && i + stringLen target < stringLen input
  && 0 <= i

{-@ concatString :: x:String -> y:String -> {v:String | v == concatString x y && stringLen v == stringLen x + stringLen y } @-}
concatString :: String -> String -> String
concatString = undefined 

{-@ stringLen    :: s:String -> {v:Int | v == stringLen s} @-}
stringLen :: String -> Int 
stringLen = length 

{-@ subString  :: s:String -> offset:Int -> ln:Int -> {v:String |v == subString s offset ln } @-}
subString :: String -> Int -> Int -> String 
subString = undefined 
