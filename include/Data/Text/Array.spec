module spec Data.Text.Array where

unsafeIndex' :: a:Data.Text.Array.Array
             -> o:Int
             -> l:Int
             -> i:{v:Int | v < (o + l)}
             -> {v:Word16 | (((v >= 56320) && (v <= 57343))
                             ? (numchars(a, o, (i-o)+1)
                                = (1 + numchars(a, o, (i-o)-1)))
                             : (numchars(a, o, (i-o)+1)
                                = (1 + numchars(a, o, i-o))))}

embed Word16 as int
