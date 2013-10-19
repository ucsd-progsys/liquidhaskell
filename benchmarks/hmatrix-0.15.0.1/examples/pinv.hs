import Numeric.LinearAlgebra
import Graphics.Plot
import Text.Printf(printf)

expand :: Int -> Vector Double -> Matrix Double
expand n x = fromColumns $ map (x^) [0 .. n]

polynomialModel :: Vector Double -> Vector Double -> Int
                -> (Vector Double -> Vector Double)
polynomialModel x y n = f where
    f z = expand n z <> ws
    ws  = expand n x <\> y

main = do
    [x,y] <- (toColumns . readMatrix) `fmap` readFile "data.txt"
    let pol = polynomialModel x y
    let view = [x, y, pol 1 x, pol 2 x, pol 3 x]
    putStrLn $ "  x      y      p 1    p 2    p 3"
    putStrLn $ format "  " (printf "%.2f") $ fromColumns view
    mplot view
