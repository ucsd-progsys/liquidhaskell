-- Numerical differentiation

import Numeric.GSL

d :: (Double -> Double) -> (Double -> Double)
d f x = fst $ derivCentral 0.01 f x

main = print $ d (\x-> x * d (\y-> x+y) 1) 1
