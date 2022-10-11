{-@ LIQUID "--exactdc"      @-}
{-@ LIQUID "--higherorder"  @-}
module ReflectBooleanFunctions where


{-@ reflect foo @-}
foo :: (Int -> Bool) -> (Int -> Bool) -> Bool 
foo f g = (f 1) && (g 1)
