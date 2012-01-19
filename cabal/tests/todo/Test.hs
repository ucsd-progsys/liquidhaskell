module Geometry  
( myP
, myFun
, sphereV
, sphereArea  
, cubeVolume  
, cubeArea  
, cuboidArea  
, cuboidVolume  
) where  

myP :: Float -> Float
myP x = 3

myFun :: Float -> Float -> Float -> Float
myFun x y z = x + y + z + (sphereV 1.0)
--myFun x y z = x + y + z
--myFun x y z = y
  
sphereV :: Float -> Float  
sphereV radius = (4.0 / 3.0) * pi * (radius ^ 3)  
  
sphereArea :: Float -> Float  
sphereArea radius = 4 * pi * (radius ^ 2)  
  
cubeVolume :: Float -> Float  
cubeVolume side = cuboidVolume side side side  
  
cubeArea :: Float -> Float  
cubeArea side = cuboidArea side side side  
  
cuboidVolume :: Float -> Float -> Float -> Float  
cuboidVolume a b c = rectangleArea a b * c  
  
cuboidArea :: Float -> Float -> Float -> Float  
cuboidArea a b c = rectangleArea a b * 2 + rectangleArea a c * 2 + rectangleArea c b * 2  
  
rectangleArea :: Float -> Float -> Float  
rectangleArea a b = a * b  
