module spec Data.Tuple where

measure fst :: (a, b) -> a
fst (a, b) = a

measure snd :: (a, b) -> b
snd (a, b) = b

qualif Fst(__v:a, __y:b): (__v = (fst __y))
qualif Snd(__v:a, __y:b): (__v = (snd __y))


fst :: {f:(x:(a,b) -> {v:a | v = (fst x)}) | f == fst }
snd :: {f:(x:(a,b) -> {v:b | v = (snd x)}) | f == snd }
