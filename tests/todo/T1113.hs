{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}
module Unit where

import Language.Haskell.Liquid.ProofCombinators

{-@ data Iso a b = Iso { isoTo   :: a -> b
                       , isoFrom :: b -> a
                       , isoTof  :: y:b -> { isoTo (isoFrom y) == y }
                       , isoFot  :: x:a -> { isoFrom (isoTo x) == x }
                       }
@-}
data Iso a b = Iso { isoTo   :: a -> b
                   , isoFrom :: b -> a
                   , isoTof  :: b -> Proof
                   , isoFot  :: a -> Proof
                   }


{-@ data MyUnit = MyUnit @-}
data MyUnit = MyUnit

data U1 p = U1
{-@ data M1 i c f p = M1 { unM1 :: (f p) } @-}
data M1 i c f p = M1 { unM1 :: f p }
data D
data C
type D1 = M1 D
type C1 = M1 C

data A
data B

type RepMyUnit = D1 A (C1 B U1)

isoMyUnit :: Iso MyUnit (RepMyUnit x)
isoMyUnit = Iso undefined undefined undefined undefined -- fromMyUnit toMyUnit fotMyUnit tofMyUnit

