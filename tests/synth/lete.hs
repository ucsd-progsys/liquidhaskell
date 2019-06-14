{-@ LIQUID "--typed-holes" @-}

{-@ lete :: { i:Int | i > 41 } @-}
lete :: Int
lete =
    let x = _x in
    x + x
