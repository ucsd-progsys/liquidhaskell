{-@ LIQUID "--reflection" @-}

{-# LANGUAGE ExistentialQuantification, KindSignatures, TypeFamilies, GADTs #-}

module ExactGADT9 where

import ExactGADT8Lib

{-@ reflect bar @-}
bar :: RefinedFilter Blob typ -> Bool
bar (RefinedFilter BlobXVal) = True
bar (RefinedFilter BlobYVal) = True
