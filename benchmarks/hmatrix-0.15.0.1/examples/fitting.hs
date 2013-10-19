-- nonlinear least-squares fitting

import Numeric.GSL.Fitting
import Numeric.LinearAlgebra

xs = map return [0 .. 39]
sigma = 0.1
ys = map return $ toList $ fromList (map (head . expModel [5,0.1,1]) xs)
            + scalar sigma * (randomVector 0 Gaussian 40)

dat :: [([Double],([Double],Double))]

dat = zip xs (zip ys (repeat sigma))

expModel [a,lambda,b] [t] = [a * exp (-lambda * t) + b]

expModelDer [a,lambda,b] [t] = [[exp (-lambda * t), -t * a * exp(-lambda*t) , 1]]

(sol,path) = fitModelScaled 1E-4 1E-4 20 (expModel, expModelDer) dat [1,0,0]

main = do
    print dat
    print path
    print sol
