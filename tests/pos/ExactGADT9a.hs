{-@ LIQUID "--exact-data-con" @-}

{-# LANGUAGE ExistentialQuantification, KindSignatures, TypeFamilies, GADTs #-}

module ExactGADT9a where

import ExactGADT8a

{-@ reflect zoo @-}
zoo :: EntityField a -> Bool 
zoo BlobXVal = True 
zoo BlobYVal = False 

