-- Numerical integration
import Numeric.GSL

quad f a b = fst $ integrateQAGS 1E-9 100 f a b  

-- A multiple integral can be easily defined using partial application
quad2 f y1 y2 g1 g2 = quad h y1 y2
  where
    h y = quad (flip f y) (g1 y) (g2 y)

volSphere r = 8 * quad2 (\x y -> sqrt (r*r-x*x-y*y)) 
                        0 r (const 0) (\x->sqrt (r*r-x*x))

-- wikipedia example
exw = quad2 f 7 10 (const 11) (const 14)
  where
    f x y = x**2 + 4*y

main = do
    print $ quad (\x -> 4/(x^2+1)) 0 1
    print pi
    print $ volSphere 2.5
    print $ 4/3*pi*2.5**3
    print $ exw
