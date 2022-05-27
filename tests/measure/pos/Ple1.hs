-- this tests reflection + PLE + holes

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Ple1 where

import Ple1Lib 

{-@ check :: { adder 10 20 == 30 } @-}
check = ()

imports = ( adder ) 
