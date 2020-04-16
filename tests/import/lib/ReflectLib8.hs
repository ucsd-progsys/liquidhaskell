-- By Zack Grannan at https://github.com/ucsd-progsys/liquidhaskell/pull/1646

{-@ LIQUID "--reflection" @-}
module ReflectLib8 where

{-@ reflect choose @-}
choose _ b = b

{-@ reflect chooseF @-}
chooseF f g x =
  choose (f x) (g x)