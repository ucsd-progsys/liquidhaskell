data Bits = O Bits | I Bits | O' deriving Show

type Sq = Int
type Mul = Int

zero, one, two, three, four :: Bits
zero = O'
one = I O'
two = O (I O')
three = I (I O')
four = O (O (I O'))

hammingWeight :: Bits -> Int
hammingWeight = undefined

sam :: Int -> Bits -> ((Sq, Mul), Int)
sam _ O'     = ((0, 0), 1)
sam x (O bs) = let ((s, m), r) = sam x bs in ((1 + s, m), r * r)
sam x (I bs) = let ((s, m), r) = sam x bs in ((1 + s, 1 + m), x * r * r)

-- sam(0001) = (4, 1)
-- sam(1000) = (4, 1)

{-@ relational sam ~ sam :: x1:_ -> p1:_ -> _ ~ x2:_ -> p2:_ -> _ 
                         ~~ true => 
                              len p1 == len p2 && hammingWeight p1 == hammingWeight p2 => 
                                 fst (r1 x1 p1) == fst (r2 x2 p2) @-}
