-- Support for Strings for SMT 

{-# LANGUAGE OverloadedStrings   #-}

module Language.Haskell.Liquid.String where

import qualified Data.ByteString as BS
import qualified Data.String     as ST

{-@ embed SMTString as Str @-}

data SMTString = S BS.ByteString 
  deriving (Eq, Show)

{-@ invariant {s:SMTString | 0 <= stringLen s } @-}

{-@ measure stringEmp    :: SMTString @-}
{-@ measure stringLen    :: SMTString -> Int @-}
{-@ measure subString    :: SMTString -> Int -> Int -> SMTString @-}
{-@ measure concatString :: SMTString -> SMTString -> SMTString @-}
{-@ measure fromString   :: String -> SMTString @-}
{-@ measure takeString   :: Int -> SMTString -> SMTString @-}
{-@ measure dropString   :: Int -> SMTString -> SMTString @-}

----------------------------------

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


{-@ takeString :: i:Nat -> xs:{SMTString | i <= stringLen xs } -> {v:SMTString | stringLen v == i && v == takeString i xs } @-} 
takeString :: Int -> SMTString -> SMTString
takeString i (S s) = S (BS.take i s)

{-@ dropString :: i:Nat -> xs:{SMTString | i <= stringLen xs } -> {v:SMTString | stringLen v == stringLen xs - i && v == dropString i xs } @-} 
dropString :: Int -> SMTString -> SMTString
dropString i (S s) = S (BS.drop i s)


{-@ assume fromString :: i:String -> {o:SMTString | i == o && o == fromString i} @-}
fromString :: String -> SMTString
fromString = S . ST.fromString 


{-@ isNullString :: i:SMTString -> {b:Bool | Prop b <=> stringLen i == 0 } @-} 
isNullString :: SMTString -> Bool 
isNullString (S s) = BS.length s == 0 
