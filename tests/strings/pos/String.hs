{-# LANGUAGE OverloadedStrings   #-}

{-@ LIQUID "--higherorder"         @-}
{-@ LIQUID "--totality"            @-}
{-@ LIQUID "--exactdc"             @-}

module String where

import qualified Data.ByteString as BS
import qualified Data.String     as ST
import Language.Haskell.Liquid.ProofCombinators 


{-@ embed SMTString as Str @-}

data SMTString = S BS.ByteString 
  deriving (Eq, Show)

------------------------------------------------------------------------------
---------------  SMTString Interface in Logic --------------------------------
------------------------------------------------------------------------------


{-@ invariant {s:SMTString | 0 <= stringLen s } @-}

{-@ measure stringEmp    :: SMTString @-}
{-@ measure stringLen    :: SMTString -> Int @-}
{-@ measure subString    :: SMTString -> Int -> Int -> SMTString @-}
{-@ measure concatString :: SMTString -> SMTString -> SMTString @-}
{-@ measure fromString   :: String -> SMTString @-}
{-@ measure takeString   :: Int -> SMTString -> SMTString @-}
{-@ measure dropString   :: Int -> SMTString -> SMTString @-}

------------------------------------------------------------------------------
---------------  SMTString operators -----------------------------------------
------------------------------------------------------------------------------

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

{-@ assume takeString :: i:Nat -> xs:{SMTString | i <= stringLen xs } -> {v:SMTString | stringLen v == i && v == takeString i xs } @-} 
takeString :: Int -> SMTString -> SMTString
takeString i (S s) = S (BS.take i s)

{-@ assume dropString :: i:Nat -> xs:{SMTString | i <= stringLen xs } -> {v:SMTString | stringLen v == stringLen xs - i && v == dropString i xs } @-} 
dropString :: Int -> SMTString -> SMTString
dropString i (S s) = S (BS.drop i s)

{-@ assume fromString :: i:String -> {o:SMTString | i == o && o == fromString i} @-}
fromString :: String -> SMTString
fromString = S . ST.fromString 

{-@ assume isNullString :: i:SMTString -> {b:Bool | Prop b <=> stringLen i == 0 } @-} 
isNullString :: SMTString -> Bool 
isNullString (S s) = BS.length s == 0 

------------------------------------------------------------------------------
---------------  Properties assumed for SMTStrings ---------------------------
------------------------------------------------------------------------------

-- | Empty Strings 

{-@ assume stringEmpProp :: x:SMTString  -> { stringLen x == 0 <=> x == stringEmp } @-}
stringEmpProp :: SMTString -> Proof
stringEmpProp _ = trivial 
 
concatStringNeutralLeft :: SMTString -> Proof
{-@ assume concatStringNeutralLeft :: x:SMTString -> {concatString x stringEmp == x} @-}
concatStringNeutralLeft _ = trivial

concatStringNeutralRight :: SMTString -> Proof
{-@ assume concatStringNeutralRight :: x:SMTString -> {concatString stringEmp x == x} @-}
concatStringNeutralRight _ = trivial

{-@ concatEmpLeft :: xi:{SMTString | stringLen xi == 0} -> yi:SMTString -> {concatString xi yi == yi} @-}
concatEmpLeft :: SMTString -> SMTString -> Proof
concatEmpLeft xi yi 
  =   concatString xi yi 
  ==. concatString stringEmp yi ? stringEmpProp xi 
  ==. yi                        ? concatStringNeutralRight yi
  *** QED 


{-@ concatEmpRight :: xi:SMTString -> yi:{SMTString | stringLen yi == 0} -> {concatString xi yi == xi} @-}
concatEmpRight :: SMTString -> SMTString -> Proof
concatEmpRight xi yi 
  =   concatString xi yi 
  ==. concatString xi stringEmp ? stringEmpProp yi 
  ==. xi                        ? concatStringNeutralLeft xi 
  *** QED 

-- | Concat

{-@ assume concatTakeDrop :: i:Nat -> xs:{SMTString | i <= stringLen xs} 
    -> {xs == concatString (takeString i xs) (dropString i xs) }  @-}
concatTakeDrop :: Int -> SMTString -> Proof 
concatTakeDrop _ _ = trivial

concatLen :: SMTString -> SMTString -> Proof
{-@ assume concatLen :: x:SMTString -> y:SMTString -> { stringLen (concatString x y) == stringLen x + stringLen y } @-}
concatLen _ _ = trivial

concatStringAssoc :: SMTString -> SMTString -> SMTString -> Proof
{-@ assume concatStringAssoc :: x:SMTString -> y:SMTString -> z:SMTString 
     -> {concatString (concatString x y) z == concatString x (concatString y z) } @-}
concatStringAssoc _ _ _ = trivial


-- | Substrings 

{-@ assume subStringConcatBack :: input:SMTString -> input':SMTString -> j:Int -> i:{Int | i + j <= stringLen input }
  -> { (subString input i j == subString (concatString input input') i j) 
    && (stringLen input <= stringLen (concatString input input'))
     } @-}
subStringConcatBack :: SMTString -> SMTString -> Int -> Int -> Proof 
subStringConcatBack _ _ _ _ = trivial  


{-@ assume subStringConcatFront  
  :: input:SMTString -> input':SMTString -> j:Int -> i:Int 
  -> { (subString input i j == subString (concatString input' input) (stringLen input' + i) j)
      && (stringLen (concatString input' input) == stringLen input + stringLen input')
    } @-}
subStringConcatFront :: SMTString -> SMTString -> Int -> Int -> Proof
subStringConcatFront _ _ _ _ = trivial
