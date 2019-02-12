{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt"     @-}

{-# LANGUAGE ExistentialQuantification, KindSignatures, TypeFamilies, GADTs #-}

module ExactGADT9 where

import ExactGADT8

{-@ reflect bar @-}
bar :: RefinedFilter Blob typ -> Bool
bar (RefinedFilter BlobXVal) = True
bar (RefinedFilter BlobYVal) = True
