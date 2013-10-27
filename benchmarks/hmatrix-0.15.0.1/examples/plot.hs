import Numeric.LinearAlgebra
import Graphics.Plot
import Numeric.GSL.Special(erf_Z, erf)

sombrero n = f x y where 
    (x,y) = meshdom range range
    range = linspace n (-2,2)
    f x y = exp (-r2) * cos (2*r2) where 
        r2 = x*x+y*y

f x =  sin x + 0.5 * sin (5*x)

gaussianPDF = erf_Z
cumdist x = 0.5 * (1+ erf (x/sqrt 2))

main = do
    let x = linspace 1000 (-4,4)
    mplot [f x]
    mplot [x, mapVector cumdist x, mapVector gaussianPDF x]
    mesh (sombrero 40)