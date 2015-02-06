module Fixme where

data World = W Int
{-@ data FIO a <pre :: World -> Prop, post :: World -> a -> World -> Prop>
  = FIO (rs :: (x:World<pre> -> (a, World)<\y -> {v:World<post x y> | true}>))  @-}
data FIO a  = FIO {runState :: World -> (a, World)}

{-@ createFile :: forall <p :: Int -> World -> Prop,
                          q :: Int -> World -> Int -> World -> Prop>.
  {f::Int |- World<p f> <: World}
  {f::Int, w::World<p f>,  x::Int |- World <: World<q f w x>}
  a:Int -> FIO <p a, \x z -> {v:World<q a x z> | true}> Int @-}
createFile :: Int -> FIO Int
createFile = undefined