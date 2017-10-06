{-@ LIQUID "--exact-data-con" @-}

module T1102_LibY where 

import T1102_LibZ 

data Bar = Bar {barFoo :: Foo Int Int} 

{-@ reflect bar @-}
bar :: Bar -> Int 
bar (Bar (Foo x _)) = x 
