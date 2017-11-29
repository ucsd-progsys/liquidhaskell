{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--no-adt"      @-}
{-@ LIQUID "--exactdc"     @-}

module Bug where

import Language.Haskell.Liquid.ProofCombinators

data U1 p = U1
data M1 i c f p = M1 { unM1 :: f p }
data C
data D
type C1 = M1 C
type D1 = M1 D

data MyUnit = MyUnit deriving (Eq)

data A
data B
type RepMyUnit = D1 A (C1 B U1)

{-@ axiomatize fromMyUnit @-}
fromMyUnit :: MyUnit -> RepMyUnit x_at0x
fromMyUnit MyUnit = M1 (M1 U1)

{-@ axiomatize toMyUnit @-}
toMyUnit :: RepMyUnit x_at0x -> MyUnit
toMyUnit (M1 (M1 U1)) = MyUnit

{-@ fotMyUnit :: a:RepMyUnit x
              -> { fromMyUnit (toMyUnit a) == a }
@-}
fotMyUnit :: RepMyUnit x_at0x -> Proof
fotMyUnit z_at0y@(M1 (M1 U1))
  = ((((fromMyUnit (toMyUnit z_at0y)) ==. (fromMyUnit MyUnit))
      ==. z_at0y)
     *** QED)

{-@ tofMyUnit :: a:MyUnit
              -> { toMyUnit (fromMyUnit a) == a }
@-}
tofMyUnit :: MyUnit -> Proof
tofMyUnit z_at0y@MyUnit
  = ((((toMyUnit (fromMyUnit z_at0y)) ==. (toMyUnit (M1 (M1 U1))))
      ==. z_at0y)
     *** QED)
