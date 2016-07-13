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
import GHC.CString

import Data.Proxy 
-- Structure that defines valid indeces of a type level target 
-- symbol in a value level string

data MI (tagret :: Symbol) s where 
  MI :: IsString s => s        -- input string
                   -> [Int]    -- valid indeces of target in input
                   -> MI target s

{-@ MI :: input:s 
       -> [{i:Int | subString input i (stringLen target)  == target }]
       -> MI s @-}

-- STEP 1:    Verification of valid structures
-- CHALLENGE: String interepretations from SMT 


misafe :: MI "dog" String
misafe = MI "catdogcatsdots" [3]

miunsafe :: MI "dog" String
miunsafe = MI "catdogcatsdots" [1]
