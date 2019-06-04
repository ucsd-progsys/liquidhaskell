{-@ LIQUID "--typed-holes" @-}

{-@ fortytwo :: { i:Int | i > 41 } @-}
fortytwo :: Int
fortytwo = _fortytwo

{-@ letfortytwo :: { i:Int | i > 41 } @-}
letfortytwo :: Int
letfortytwo =
    let x = _x in
    x + x
