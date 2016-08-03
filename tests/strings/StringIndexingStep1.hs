{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs               #-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--stringtheory"    @-}

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
       -> [{i:Int |	 substring input i (stringLen target)  == target }]
       -> MI s @-}

{-@ measure substring :: String -> Int -> Int -> String @-}
{-@ measure stringLen :: String -> Int @-}


-- STEP 1:    Verification of valid structures
-- CHALLENGE: String interepretations from SMT 

{-@ embed GHC.Types.Char as Char @-}

-- THESE SHOULD BE SAFE 
misafe1 :: MI "cat" String 
misafe1 = MI "catdogcatsdots" []

misafe2 :: MI "cat" String
misafe2 = MI "catdogcatsdots" [1]

misafe3 :: MI "cat" String
misafe3 = MI "catdogcatsdots" [1, 7]

misafe4 :: MI "cat" String
misafe4 = MI "catdogcatsdots" [7, 1]

misafe5 :: MI "cat" String
misafe5 = MI "catdogcatsdots" [7]


-- THIS SHOULD BE UNSAFE 
miunsafe :: MI "dog" String
miunsafe = MI "catdogcatsdots" [1]
