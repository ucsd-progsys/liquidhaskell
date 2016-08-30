module Language.Haskell.Liquid.String where

{-@ embed SMTString as Str @-}

data SMTString = S String 
  deriving Eq 

{-@ measure stringEmp    :: SMTString @-}
{-@ measure stringLen    :: SMTString -> Int @-}
{-@ measure subString    :: SMTString -> Int -> Int -> SMTString @-}
{-@ measure concatString :: SMTString -> SMTString -> SMTString @-}
{-@ measure fromString   :: String -> SMTString @-}

{-@ assume concatString :: x:SMTString -> y:SMTString 
                 -> {v:SMTString | v == concatString x y && stringLen v == stringLen x + stringLen y } @-}
concatString :: SMTString -> SMTString -> SMTString
concatString = undefined

{-@ stringEmp :: {v:SMTString | v == stringEmp  && stringLen v == 0 } @-}
stringEmp :: SMTString
stringEmp = undefined 

stringLen :: SMTString -> Int  
{-@ stringLen :: x:SMTString -> {v:Nat | v == stringLen x} @-}
stringLen = undefined


{-@ subString  :: s:SMTString -> offset:Int -> ln:Int -> {v:SMTString | v == subString s offset ln } @-}
subString :: SMTString -> Int -> Int -> SMTString 
subString = undefined 

{-@ fromString :: i:String -> {o:SMTString | i == o && o == fromString i} @-}
fromString :: String -> SMTString
fromString = undefined 