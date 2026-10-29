{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
module LfModLfDiv () where

import Language.Haskell.Liquid.Prelude (isEven)

{-@ type Even = {v:Int | lfMod v 2 = 0} @-}

{-@ checkEven :: n:Int -> {v:Bool | v <=> isEven n} @-}
checkEven = isEven

{-@ halfReal :: x:Float -> y:{Float | y /= 0.0} -> {v:Float | v = x / y} @-}
halfReal x y = x / y
