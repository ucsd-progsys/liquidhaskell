{-# LANGUAGE Rank2Types #-}

{-@ data Label<label :: User -> Bool> where @-}
data Label
data User
data Tagged l a = Tag a
data MyFunctor f = MyFunctor { myFmap :: forall a b. (a -> b) -> f a -> f b }

instance Functor (Tagged l) where
  fmap = fmapTagged

taggedFunctor :: MyFunctor (Tagged l)
taggedFunctor = MyFunctor fmapTagged

fmapTagged :: (a -> b) -> Tagged l a -> Tagged l b
fmapTagged f (Tag x) = Tag (f x)

{-@
myFmapPreservesLabel :: forall <label :: User -> Bool>.
(a -> b) -> Tagged (Label<label>) a -> Tagged (Label<label>) b
@-}
myFmapPreservesLabel :: (a -> b) -> Tagged Label a -> Tagged Label b
myFmapPreservesLabel = myFmap taggedFunctor

{-@
fmapPreservesLabel :: forall <label :: User -> Bool>.
(a -> b) -> Tagged (Label<label>) a -> Tagged (Label<label>) b
@-}
fmapPreservesLabel :: (a -> b) -> Tagged Label a -> Tagged Label b
fmapPreservesLabel = fmap