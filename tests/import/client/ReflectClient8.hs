-- By Zack Grannan at https://github.com/ucsd-progsys/liquidhaskell/pull/1646

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--extensionality" @-}

module ReflectClient8 where

import ReflectLib8

{-@ assume extensionality :: f:(a -> b) -> g:(a -> b) -> (x:a -> {f x == g x}) ->  {f == g}  @-}
extensionality :: (a -> b) -> (a -> b) -> (a -> ()) -> ()
extensionality _ _ _ = ()

{-@ refineExt' ::
        f  : (a -> Int)
     -> g  : (a -> Int)
     -> (x : a -> { v : () | Refines (f x) (g x)})
     -> x  : a
     -> {v : () | chooseF f g x = g x}
@-}
refineExt' :: (a -> Int) -> (a -> Int) -> (a -> ()) -> a -> ()
refineExt' _ _ proof x = proof x

{-@ refineExt ::
        f  : (a -> Int)
     -> g  : (a -> Int)
     -> (x : a -> { v : () | Refines (f x) (g x)})
     -> {v : () | RefinesF f g}
@-}
refineExt :: (a -> Int) -> (a -> Int) -> (a -> ()) -> ()
refineExt f g proof =
  extensionality (chooseF f g) g (refineExt' f g proof)

{-@ predicate Refines  M1 M2 = choose   M1 M2 = M2 @-}
{-@ predicate RefinesF F1 F2 = chooseF F1 F2 = F2 @-}
