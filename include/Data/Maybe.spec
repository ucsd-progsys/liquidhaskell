module spec Data.Maybe where

measure isJust :: forall a. Data.Maybe.Maybe a -> GHC.Types.Bool 
isJust (Data.Maybe.Just x)  = True
isJust (Data.Maybe.Nothing) = False

measure fromJust :: forall a. Data.Maybe.Maybe a -> a
fromJust (Data.Maybe.Just x) = x
