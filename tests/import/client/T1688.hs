{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}

module T1688 where

import T1688Lib

data HasFType where
    FTBC   :: Bool -> HasFType

{-@ ftypSize :: HasFType -> { n:Int | n >= 0 } @-}
ftypSize :: HasFType -> Int
ftypSize (FTBC {}) = 1
