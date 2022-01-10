{-# LANGUAGE GADTs #-}

{-@ LIQUID "--exact-data-cons" @-}

-- With a refinement type embedded in a function using a fieldname, but with a
-- bad type

module GADTFields03 where

{-@
data T a where
  T :: { getT :: Int, getT' :: { v:Int | v >= 0 } } -> T Int
  S :: { getT :: Int, getS :: Float } -> T Int
 @-}
data T a where
  T :: { getT :: Int, getT' :: Int } -> T Int
  S :: { getT :: Int, getS :: Float } -> T Int

{-@
measure isT
isT :: T Int -> Bool
@-}
isT :: T Int -> Bool
isT (T _ _) = True
isT _ = False

{-@ f :: { v: T Int | isT v && getS v >= 0  } -> Float @-}
f :: T Int -> Float
f = getS

main :: IO ()
main = print (f (S 5 0.1))
