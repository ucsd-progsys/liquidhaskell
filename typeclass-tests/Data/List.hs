{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.List where
import Prelude hiding (id)

import Data.Function

{-@ data List a = Nil | Cons {lh::a, lt::List a} @-}
data List a = Nil | Cons a (List a)

{-@ reflect foldrList @-}
foldrList :: (a -> b -> b) -> b -> List a -> b
foldrList _ x Nil         = x
foldrList f x (Cons y ys) = f y (foldrList f x ys)


{-@ reflect foldlList @-}
foldlList :: (b -> a -> b) -> b -> List a -> b
foldlList _ x Nil         = x
foldlList f x (Cons y ys) = foldlList f (f x y) ys


{-@ reflect appendL @-}
appendL :: List a -> List a -> List a
appendL Nil         ys = ys
appendL (Cons x xs) ys = Cons x (appendL xs ys)

{-@ appendLNil :: xs:List a -> {appendL xs Nil == xs} @-}
appendLNil :: List a -> ()
appendLNil Nil         = ()
appendLNil (Cons x xs) = appendLNil xs

{-@ appendLAssoc :: xs:List a -> ys:List a -> zs:List a -> {appendL (appendL xs ys) zs == appendL xs (appendL ys zs)} @-}
appendLAssoc :: List a -> List a -> List a -> ()
appendLAssoc Nil         _  _  = ()
appendLAssoc (Cons _ xs) ys zs = appendLAssoc xs ys zs

{-@ reflect fmapList @-}
fmapList :: (a -> b) -> List a -> List b
fmapList f Nil = Nil
fmapList f (Cons x xs) = Cons (f x) (fmapList f xs)


{-@ fmapListId :: x:List a -> {fmapList id x == id x}  @-}
fmapListId :: List a -> ()
fmapListId Nil = ()
fmapListId (Cons _ xs) = fmapListId xs

{-@ fmapListComposition :: forall a b c. f:(b -> c) -> g:(a -> b) -> x:List a -> {fmapList (compose f g) x == compose (fmapList f) (fmapList g) x} @-}
fmapListComposition :: forall a b c. (b -> c) -> (a -> b) -> List a -> ()
fmapListComposition f g Nil = ()
fmapListComposition f g (Cons _ xs) = fmapListComposition f g xs

{-@ fmapListResAppend :: f:(a -> b) -> xs:List a -> ys:List a -> {fmapList f (appendL xs ys) == appendL (fmapList f xs) (fmapList f ys)} @-}
fmapListResAppend :: (a -> b) -> List a -> List a -> ()
fmapListResAppend f Nil         ys = ()
fmapListResAppend f (Cons _ xs) ys = fmapListResAppend f xs ys
