{-@ LIQUID "--no-totality"    @-}

-- see https://github.com/ucsd-progsys/liquidhaskell/issues/866

module T866 where 

data Body = Body Int Int 

genBody :: [Int] -> Body
genBody s   = Body x y 
  where 
    (x:y:_) = s

