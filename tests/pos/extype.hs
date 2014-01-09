{-# LANGUAGE ExistentialQuantification, MultiParamTypeClasses #-}
module ExTy () where

class Show (layout a) => LayoutClass layout a where

data Layout a = forall l. Layout (l a)


readsLayout :: Layout a -> String -> Layout a
readsLayout (Layout l) s = Layout (asTypeOf undefined l)

type Size = Int
data Step s a = S s a

data Stream a =
    forall s. Stream
    (s -> Step s a)             -- stepper function
    !s                          -- current state
    !Size                       -- size hint


foo :: Stream a -> Size
foo (Stream _ _ s) = s


stream = Stream (\_ -> S 1 True) 0 0
