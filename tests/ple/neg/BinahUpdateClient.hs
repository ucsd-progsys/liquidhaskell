{-@ LIQUID "--no-adt" 	                           @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}
{-@ LIQUID "--ple" @-} 

{-# LANGUAGE ExistentialQuantification, KindSignatures, TypeFamilies, GADTs #-}

module BinahUpdateClient where

import BinahUpdateLib 

testUpdateQuery :: () -> Update Blob Int
testUpdateQuery () = createUpdate BlobXVal 8  -- toggle to 80 to be SAFE 
