{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs               #-}
{-@ LIQUID "--totality"        @-}

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
       -> [{i:Int |	 str.substr input i (str.len target)  == target }]
       -> MI s @-}

-- STEP 1:    Verification of valid structures
-- CHALLENGE: String interepretations from SMT 


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


-- STEP 2: Verify that mempty and mappend satisfy the invariants 
{-@ axiomatize mempty @-}
mempty :: forall (target :: Symbol). MI target String
mempty = MI "" []

{-@ axiomatize mappend @-}
mappend :: forall (target :: Symbol). (KnownSymbol target) => MI target String -> MI target String -> MI target String
mappend (MI i1 is1) (MI i2 is2)
  = MI input (is1 ++ (map (+ length i1) is2) ++ is)
  where 
  	is     = filter (\i -> substr input i len  == target) [(len1 - len) .. (len1 + len)]
  	input  = i1 ++ i2 
  	len1   = length i1 
  	len    = length target 
  	target = symbolVal (Proxy :: Proxy target)


substr :: IsString s => s -> Int -> Int -> s 
substr = undefined 


-- STEP 3: Verify that mempty and mappend satisfy the monoid laws

mempty_left      :: forall (target :: Symbol) s. IsString s => MI target s -> ()
{-@ mempty_left  :: x:MI target s -> {mappend mempty x == x } @-}
mempty_left _    = undefined 


mempty_right     :: forall (target :: Symbol) s. IsString s => MI target s -> ()
{-@ mempty_right :: x:MI target s -> {mappend x mempty == x } @-}
mempty_right _   = undefined 

mappend_assoc     :: forall (target :: Symbol) s. IsString s => MI target s -> MI target s -> MI target s -> ()
{-@ mappend_assoc :: x:MI target s -> y:MI target s -> z:MI target s 
                  -> {mappend x (mappend y z) == mappend (mappend x y) z } @-}
mappend_assoc _ _ _ = undefined 
