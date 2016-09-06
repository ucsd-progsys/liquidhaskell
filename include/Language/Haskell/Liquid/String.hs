{-# LANGUAGE OverloadedStrings   #-}

module Language.Haskell.Liquid.String where

import qualified Data.ByteString as BS
import qualified Data.String     as ST
import Language.Haskell.Liquid.ProofCombinators 


{-@ embed SMTString as Str @-}

data SMTString = S BS.ByteString 
  deriving (Eq, Show)

{-@ invariant {s:SMTString | 0 <= stringLen s } @-}

{-@ measure stringEmp    :: SMTString @-}
{-@ measure stringLen    :: SMTString -> Int @-}
{-@ measure subString    :: SMTString -> Int -> Int -> SMTString @-}
{-@ measure concatString :: SMTString -> SMTString -> SMTString @-}
{-@ measure fromString   :: String -> SMTString @-}

{-@ assume concatString :: x:SMTString -> y:SMTString 
                 -> {v:SMTString | v == concatString x y && stringLen v == stringLen x + stringLen y } @-}
concatString :: SMTString -> SMTString -> SMTString
concatString (S s1) (S s2) = S (s1 `BS.append` s2)

{-@ assume stringEmp :: {v:SMTString | v == stringEmp  && stringLen v == 0 } @-}
stringEmp :: SMTString
stringEmp = S (BS.empty)

stringLen :: SMTString -> Int  
{-@ assume stringLen :: x:SMTString -> {v:Nat | v == stringLen x} @-}
stringLen (S s) = BS.length s 


{-@ assume subString  :: s:SMTString -> offset:Int -> ln:Int -> {v:SMTString | v == subString s offset ln } @-}
subString :: SMTString -> Int -> Int -> SMTString 
subString (S s) o l = S (BS.take l $ BS.drop o s) 

{-@ assume fromString :: i:String -> {o:SMTString | i == o && o == fromString i} @-}
fromString :: String -> SMTString
fromString = S . ST.fromString 


chunkString :: Int -> SMTString -> [SMTString]
chunkString n s | n <= 0 = [s] 
chunkString n (S s) = S <$> go s 
  where
    go s | BS.length s <= n = [s]
    go s = let (x, rest) = BS.splitAt n s in x:go rest 


{-@ isNullString :: i:SMTString -> {b:Bool | Prop b <=> stringLen i == 0 } @-} 
isNullString :: SMTString -> Bool 
isNullString (S s) = BS.length s == 0 



-- Properties of SMTString 


{-@ assume subStringConcat 
  :: input:SMTString -> input':SMTString -> j:Int -> i:{Int | i + j <= stringLen input }
  -> { subString input i j == subString (concatString input input') i j } @-}
subStringConcat :: SMTString -> SMTString -> Int -> Int -> Proof 
subStringConcat = undefined  


{-@ assume subStringConcatFront  
  :: input:SMTString -> input':SMTString -> j:Int -> i:Int 
  -> { subString input i j == subString (concatString input' input) (stringLen input' + i) j } @-}
subStringConcatFront :: SMTString -> SMTString -> Int -> Int -> Proof
subStringConcatFront = undefined 

{-@ assume lenConcat 
  :: input:SMTString -> input':SMTString 
  -> { stringLen input <= stringLen (concatString input input') } @-}
lenConcat :: SMTString -> SMTString -> Proof 
lenConcat = undefined 


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