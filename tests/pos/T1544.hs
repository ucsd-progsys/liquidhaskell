{-@ LIQUID "--reflection"    @-}
module T1544 where

{-@ data ThingMM = ThingMM {f :: Int -> Int, fprop :: v:Int -> {f v >= 0}} @-}
data ThingMM =
  ThingMM
    { f :: Int -> Int
    , fprop :: Int -> ()
    }

{-@ fieldLemmaPat :: t:ThingMM -> v:Int -> {f t v >= 0} @-}
fieldLemmaPat :: ThingMM -> Int -> ()
fieldLemmaPat (ThingMM _ fprop) i = const () $ fprop i

{-@ fieldLemmaSel :: t:ThingMM -> v:Int -> {f t v >= 0} @-}
fieldLemmaSel :: ThingMM -> Int -> ()
fieldLemmaSel t i = const () $ fprop t i
