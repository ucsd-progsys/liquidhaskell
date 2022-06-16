{-@ LIQUID "--expect-error-containing=one or more fields in the data declaration for `A`" @-}
-- | see: https://github.com/ucsd-progsys/liquidhaskell/issues/1169

module EmptyData where

{-@ data A @-}
data A = B
