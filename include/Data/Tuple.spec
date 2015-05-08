module spec Data.Tuple where

fst :: x:(a,b) -> {v:a | v = (fst x)}
snd :: x:(a,b) -> {v:b | v = (snd x)}