{-@ LIQUID "--exactdc" @-}

module B where 

import A 

data Bar = Bar {barFoo :: Foo Int Int} 
{-@ data Bar = Bar {barFoo :: Foo} @-}

{-@ reflect bar @-}
bar :: Bar -> Int 
bar (Bar (Foo x _)) = x 