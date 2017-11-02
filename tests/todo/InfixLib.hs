module InfixLib where 

{-@ infix +++ @-}
{-@ reflect +++ @-}
(+++) :: Int -> Int -> Int 
a +++ b = a + b + 10 

