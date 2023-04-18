module spec Control.Parallel.Strategies where

assume Control.Parallel.Strategies.withStrategy :: Control.Parallel.Strategies.Strategy a -> x:a -> {v:a | v == x}
