{-@ LIQUID "--expect-any-error" @-}
-- this tests reflection + PLE + holes

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Ple1 where

import Ple1Lib 

{-@ check :: _ -> { adder 10 20 == 300 } @-}
check () = ()

