{-@ LIQUID "--exactdc"     @-}
{-@ LIQUID "--higherorder" @-}

module Bug where


{-@ data Par1 p = Par1 { unPar1 :: p } @-}
data Par1 p = Par1 { unPar1 :: p }


{-@ reflect eqPar1 @-}
eqPar1 :: (p -> p -> Bool) -> Par1 p -> Par1 p -> Bool
eqPar1 eqP x y = eqP (unPar1 x) (unPar1 y)
