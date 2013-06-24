module spec Data.Maybe where

measure isJust :: forall a. Maybe a -> Prop
isJust (Just x)  = true
isJust (Nothing) = false

measure fromJust :: forall a. Maybe a -> a
fromJust (Just x) = x
