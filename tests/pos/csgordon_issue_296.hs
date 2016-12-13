module BadMeasureType where 

{-@ measure fwd_extends :: IO () -> IO () -> Bool @-}
{-@ assume fwd_extends_refl :: m:IO () -> {v:Bool | (fwd_extends m m)} @-}
fwd_extends_refl :: IO () -> Bool
fwd_extends_refl = undefined
