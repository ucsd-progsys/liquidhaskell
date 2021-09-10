module ReExportClient where 

import ReExport 

{-@ bar :: Foo -> {v:Int | 0 < v} @-} 
bar :: Foo -> Int 
bar (Foo x) = x 