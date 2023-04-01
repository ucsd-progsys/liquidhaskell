module spec Data.Tuple where

fst :: {f:(x:(a,b) -> {v:a | v = (fst x)}) | f == fst }
snd :: {f:(x:(a,b) -> {v:b | v = (snd x)}) | f == snd }
