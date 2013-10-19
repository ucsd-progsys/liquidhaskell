-- The magic of Lie Algebra

import Numeric.LinearAlgebra

disp = putStrLn . dispf 5

rot1 :: Double -> Matrix Double
rot1 a = (3><3)
 [ 1, 0, 0
 , 0, c, s
 , 0,-s, c ]
    where c = cos a
          s = sin a

g1,g2,g3 :: Matrix Double

g1 = (3><3) [0, 0,0
            ,0, 0,1
            ,0,-1,0]

rot2 :: Double -> Matrix Double
rot2 a = (3><3)
 [ c, 0, s
 , 0, 1, 0
 ,-s, 0, c ]
    where c = cos a
          s = sin a

g2 = (3><3) [ 0,0,1
            , 0,0,0
            ,-1,0,0]

rot3 :: Double -> Matrix Double
rot3 a = (3><3)
 [ c, s, 0
 ,-s, c, 0
 , 0, 0, 1 ]
    where c = cos a
          s = sin a

g3 = (3><3) [ 0,1,0
            ,-1,0,0
            , 0,0,0]

deg=pi/180

-- commutator
infix 8 &
a & b = a <> b - b <> a

infixl 6 |+|
a |+| b = a + b + a&b /2  + (a-b)&(a & b) /12

main = do
   let a =  45*deg
       b =  50*deg
       c = -30*deg
       exact = rot3 a <> rot1 b <> rot2 c
       lie = scalar a * g3 |+| scalar b * g1 |+| scalar c * g2
   putStrLn "position in the tangent space:"
   disp lie
   putStrLn "exponential map back to the group (2 terms):"
   disp (expm lie)
   putStrLn "exact position:"
   disp exact
