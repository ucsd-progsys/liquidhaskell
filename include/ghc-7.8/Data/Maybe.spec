module spec Data.Maybe where

measure isJust :: forall a. Data.Maybe.Maybe a -> Prop
isJust (Data.Maybe.Just x)  = true
isJust (Data.Maybe.Nothing) = false

measure fromJust :: forall a. Data.Maybe.Maybe a -> a
fromJust (Data.Maybe.Just x) = x
