import Numeric.LinearAlgebra
import Graphics.Plot

vector l = fromList l :: Vector Double
matrix ls = fromLists ls :: Matrix Double
diagl = diag . vector

f = matrix [[1,0,0,0],
            [1,1,0,0],
            [0,0,1,0],
            [0,0,0,1]]

h = matrix [[0,-1,1,0],
            [0,-1,0,1]]

q = diagl [1,1,0,0]

r = diagl [2,2]

s0 = State (vector [0, 0, 10, -10]) (diagl [10,0, 100, 100])

data System = System {kF, kH, kQ, kR :: Matrix Double}
data State = State {sX :: Vector Double , sP :: Matrix Double}
type Measurement = Vector Double

kalman :: System -> State -> Measurement -> State
kalman (System f h q r) (State x p) z = State x' p' where
    px = f <> x                            -- prediction
    pq = f <> p <> trans f + q             -- its covariance
    y  = z - h <> px                       -- residue
    cy = h <> pq <> trans h + r            -- its covariance
    k  = pq <> trans h <> inv cy           -- kalman gain
    x' = px + k <> y                       -- new state
    p' = (ident (dim x) - k <> h) <> pq    -- its covariance

sys = System f h q r

zs = [vector [15-k,-20-k] | k <- [0..]]

xs = s0 : zipWith (kalman sys) xs zs

des = map (sqrt.takeDiag.sP) xs

evolution n (xs,des) =
    vector [1.. fromIntegral n]:(toColumns $ fromRows $ take n (zipWith (-) (map sX xs) des)) ++
    (toColumns $ fromRows $ take n (zipWith (+) (map sX xs) des))

main = do
    print $ fromRows $ take 10 (map sX xs)
    mapM_ (print . sP) $ take 10 xs
    mplot (evolution 20 (xs,des))
