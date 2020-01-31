{-@ LIQUID "--typed-holes" @-}

{-@ lete :: { i:Int | i > 41 } @-}
lete :: Int
lete =
------------------------------------------------------
    -- type annotated `x = _x :: Int` not in holesMap
    -- without type annotation `_x` isn't `Int`
    -- What happens in this case? 
------------------------------------------------------
    let x = _x in   
    x + x
