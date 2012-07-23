{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE CPP, NoImplicitPrelude, MagicHash #-}
{-# OPTIONS_HADDOCK hide #-}

module GHC.List (
 null
 -- reverse , 
 --foldr1
 --, length
 ) where

import Data.Maybe
import GHC.Base hiding (assert) 
import Language.Haskell.Liquid.Prelude (crash)

{-@ assert null :: forall a. xs:[a] -> {v: Bool | ((? v) <=> len(xs) = 0) }  @-}
null                    :: [a] -> Bool
null []                 =  True
null (_:_)              =  False

--{- include <len.hquals> @-}
--{- assert reverse :: xs:[a] -> {v: [a] | len(v) = len(xs)} @-}
--reverse :: [a] -> [a]
--reverse l =  rev l []
--  where rev []     a = a
--        rev (x:xs) a = rev xs (x:a)

{-@ assert errorEmptyList :: {v: String | (0 = 1)} -> a @-}

--errorEmptyList :: String -> a
--errorEmptyList fun =
--  error (prel_list_str ++ fun ++ ": empty list")
--
--prel_list_str :: String
--prel_list_str = "Prelude."

{-@ assert foldr1 :: (a -> a -> a) -> xs:{v: [a] | len(v) > 0} -> a @-}

--foldr1            :: (a -> a -> a) -> [a] -> a
--foldr1 _ [x]      =  x
--foldr1 f (x:xs)   =  f x (foldr1 f xs)
--foldr1 _ []       =  errorEmptyList "foldr1"

--foldr1 f arg = case arg of
--                []     -> crash
--                (x:xs) -> case xs of
--                            [] -> x
--                            _  -> f x (foldr1 f xs) 












