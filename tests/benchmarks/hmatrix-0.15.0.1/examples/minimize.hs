-- the multidimensional minimization example in the GSL manual
import Numeric.GSL
import Numeric.LinearAlgebra
import Graphics.Plot
import Text.Printf(printf)

-- the function to be minimized
f [x,y] = 10*(x-1)^2 + 20*(y-2)^2 + 30

-- exact gradient
df [x,y] = [20*(x-1), 40*(y-2)]

-- a minimization algorithm which does not require the gradient
minimizeS f xi = minimize NMSimplex2 1E-2 100 (replicate (length xi) 1) f xi

-- Numerical estimation of the gradient
gradient f v = [partialDerivative k f v | k <- [0 .. length v -1]]

partialDerivative n f v = fst (derivCentral 0.01 g (v!!n)) where
    g x = f (concat [a,x:b])
    (a,_:b) = splitAt n v

disp = putStrLn . format "  " (printf "%.3f")

allMethods :: (Enum a, Bounded a) => [a]
allMethods = [minBound .. maxBound]

test method = do
    print method
    let (s,p) = minimize method 1E-2 30 [1,1] f [5,7]
    print s
    disp p

testD method = do
    print method
    let (s,p) = minimizeD method 1E-3 30 1E-2 1E-4 f df [5,7]
    print s
    disp p

testD' method = do
    putStrLn $ show method ++ " with estimated gradient"
    let (s,p) = minimizeD method 1E-3 30 1E-2 1E-4 f (gradient f) [5,7]
    print s
    disp p

main = do
    mapM_ test [NMSimplex, NMSimplex2]
    mapM_ testD allMethods
    testD' ConjugateFR
    mplot $ drop 3 . toColumns . snd $ minimizeS f [5,7]
