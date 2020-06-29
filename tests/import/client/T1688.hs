{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}

module T1688 where

import T1688Lib

-- PROBLEM: If we comment `dummy` then `Step` is not in scope and the resolution of `EFake` fails.
--dummy = (\x y -> Step x y)

data HasFType where
    FTBC   :: Bool -> HasFType

{-@ ftypSize :: HasFType -> { n:Int | n >= 0 } @-}
ftypSize :: HasFType -> Int
ftypSize (FTBC {}) = 1
