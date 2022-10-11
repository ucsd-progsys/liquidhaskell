{-@ LIQUID "--expect-error-containing=Data constructors in refinement do not match original datatype for `Hog`" @-}
{-@ LIQUID "--exact-data-cons" @-}

module BadData2 where

-- The reason this fails is because the constructor we use in the
-- refinement for Hog is in fact a constructor of T.
{-@ data Hog where  
      Cuthb :: Nat -> T 
  @-}

data Hog = H Int 

data T = Cuthb { fldX :: Int }

zoink = Cuthb (-1)
