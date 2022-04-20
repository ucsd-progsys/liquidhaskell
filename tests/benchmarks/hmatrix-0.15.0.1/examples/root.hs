-- root finding examples
import Numeric.GSL
import Numeric.LinearAlgebra
import Text.Printf(printf)

rosenbrock a b [x,y] = [ a*(1-x), b*(y-x^2) ]

test method = do
    print method
    let (s,p) = root method 1E-7 30 (rosenbrock 1 10) [-10,-5]
    print s -- solution
    disp p -- evolution of the algorithm

jacobian a b [x,y] = [ [-a    , 0]
                     , [-2*b*x, b] ]

testJ method = do
    print method
    let (s,p) = rootJ method 1E-7 30 (rosenbrock 1 10) (jacobian 1 10) [-10,-5]
    print s
    disp p

disp = putStrLn . format "  " (printf "%.3f")

main = do
    test Hybrids
    test Hybrid
    test DNewton
    test Broyden

    mapM_ testJ [HybridsJ .. GNewton]
