module DPairs where


{-@ ex :: (y::Int, () -> {v:() | 0 < y } )
  -> (y::Int, {v:() | 0 < y})
@-}
ex ::(Int,() -> ()) -> (Int,())
ex (y, pxToqxy) =  (y,pxToqxy ())