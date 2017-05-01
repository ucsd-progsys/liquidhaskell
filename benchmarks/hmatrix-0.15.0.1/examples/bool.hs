-- vectorized boolean operations defined in terms of step or cond

import Numeric.LinearAlgebra

infix  4  .==., ./=., .<., .<=., .>=., .>.
infixr 3  .&&.
infixr 2  .||.

a .<.  b = step (b-a)
a .<=. b = cond a b 1 1 0
a .==. b = cond a b 0 1 0
a ./=. b = cond a b 1 0 1
a .>=. b = cond a b 0 1 1
a .>.  b = step (a-b)

a .&&. b  = step (a*b)
a .||. b  = step (a+b)
no a      = 1-a
xor a b   = a ./=. b
equiv a b = a .==. b
imp a b   = no a .||. b

taut x = minElement x == 1

minEvery a b = cond a b a a b
maxEvery a b = cond a b b b a

-- examples

clip a b x = cond y b y y b where y = cond x a a x x

disp = putStr . dispf 3

eye n = ident n :: Matrix Double
row = asRow . fromList    :: [Double] -> Matrix Double
col = asColumn . fromList :: [Double] -> Matrix Double

m = (3><4) [1..] :: Matrix Double

p = row [0,0,1,1]
q = row [0,1,0,1]

main = do
    print $ find (>6) m
    disp $ assoc (6,8) 7 $ zip (find (/=0) (eye 5)) [10..]
    disp $ accum (eye 5) (+) [((0,2),3), ((3,1),7), ((1,1),1)]
    disp $ m .>=. 10  .||.  m .<. 4
    (disp . fromColumns . map flatten) [p, q, p.&&.q, p .||.q, p `xor` q, p `equiv` q, p `imp` q]
    print $ taut $ (p `imp` q ) `equiv` (no q `imp` no p)
    print $ taut $ (xor p q) `equiv` (p .&&. no q .||. no p .&&. q)
    disp $ clip 3 8 m
    disp $ col [1..7] .<=. row [1..5]
    disp $ cond (col [1..3]) (row [1..4]) m 50 (3*m)

