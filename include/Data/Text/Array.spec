module spec Data.Text.Array where

data Data.Text.Array.Array <p :: Int -> Prop>
     = Data.Text.Array.Array
         (aBA :: GHC.Prim.ByteArray#)
         (aLen :: {v:Int<p> | v >= 0})

measure alen :: Data.Text.Array.Array -> Int
alen (Data.Text.Array.Array aBA aLen) = aLen

invariant {v:Data.Text.Array.Array | (alen v) >= 0}

aLen :: a:Data.Text.Array.Array
     -> {v:Int | v = (alen a)}

data Data.Text.Array.MArray s <p :: Int -> Prop>
     = Data.Text.Array.MArray
         (maBA :: GHC.Prim.MutableByteArray# s)
         (maLen :: {v:Int<p> | v >= 0})

measure malen :: Data.Text.Array.MArray s -> Int
malen (Data.Text.Array.MArray maBA maLen) = maLen

maLen :: ma:(Data.Text.Array.MArray s)
      -> {v:Int | v = (malen ma)}

new :: forall s. n:{v:Int | v >= 0}
    -> (GHC.ST.ST s ({v:Data.Text.Array.MArray s | (malen v) = n}))

unsafeFreeze :: ma:Data.Text.Array.MArray s
             -> (ST s {v:Data.Text.Array.Array | (alen v) = (malen ma)})

-- unsafeFreeze :: forall <p :: Int -> Prop>.
--                 Data.Text.Array.MArray s <p>
--              -> (GHC.ST.ST s (Data.Text.Array.Array<p>))

unsafeIndex :: a:Data.Text.Array.Array
            -> i:{v:Int | (Btwn v 0 (alen a))}
            -> Data.Word.Word16

unsafeIndexB :: a:Data.Text.Array.Array
             -> o:{v:Int | (Btwn v 0 (alen a))}
             -> l:{v:Int | ((v >= 0) && ((o+v) <= (alen a)))}
             -> i:{v:Int | (Btwn (v) (o) (o + l))}
             -> {v:Data.Word.Word16 | (((v >= 56320) && (v <= 57343))
                                       ? ((numchars(a, o, (i-o)+1)
                                           = (1 + numchars(a, o, (i-o)-1)))
                                          && (((i-o)-1) >= 0))
                                       : (numchars(a, o, (i-o)+1)
                                          = (1 + numchars(a, o, i-o))))}

unsafeIndexF :: a:Data.Text.Array.Array
             -> o:{v:Int | (Btwn v 0 (alen a))}
             -> l:{v:Int | ((v >= 0) && ((o+v) <= (alen a)))}
             -> i:{v:Int | (Btwn (v) (o) (o + l))}
             -> {v:Data.Word.Word16 | (((v >= 55296) && (v <= 56319))
                                       ? ((numchars(a, o, (i-o)+1)
                                           = (1 + numchars(a, o, (i-o)-1)))
                                          && (((i-o)+1) < l))
                                       : (numchars(a, o, (i-o)+1)
                                          = (1 + numchars(a, o, i-o))))}

unsafeWrite :: ma:(Data.Text.Array.MArray s)
            -> i:{v:Int | (Btwn v 0 (malen ma))}
            -> Data.Word.Word16
            -> (GHC.ST.ST s ())

toList :: a:{v:Data.Text.Array.Array | (alen v) >= 0}
       -> o:{v:Int | (BtwnI v 0 (alen a))}
       -> l:{v:Int | ((v >= 0) && ((v+o) <= (alen a)))}
       -> {v:[Data.Word.Word16] | (len v) = l}

empty :: {v:Data.Text.Array.Array | (alen v) = 0}

-- run :: forall <p :: Int -> Prop>.
--        (forall s. GHC.ST.ST s (Data.Text.Array.MArray s <p>))
--     -> (exists[z:Int<p>]. Data.Text.Array.Array<p>)

copyM :: ma1:(Data.Text.Array.MArray s)
      -> o1:{v:Int | ((v >= 0) && (v < (malen ma1)))}
      -> ma2:(Data.Text.Array.MArray s)
      -> o2:{v:Int | ((v >= 0) && (v < (malen ma2)))}
      -> cnt:{v:Int | ((v > 0) && ((v + o1) <= (malen ma1)) && ((v + o2) <= (malen ma2)))}
      -> (GHC.ST.ST s ())

copyI :: ma:Data.Text.Array.MArray s
      -> mo:{v:Int | ((v >= 0) && (v < (malen ma)))}
      -> a:Data.Text.Array.Array
      -> o:{v:Int | ((v >= 0) && (v < (alen a)))}
      -> top:{v:Int | ((v >= mo) && (v <= (malen ma)) && (((v-mo)+o) <= (alen a)))}
      -> (GHC.ST.ST s ())

-- equal :: a1:Data.Text.Array.Array
--       -> o1:{v:Int | ((v >= 0) && (v < (alen a1)))}
--       -> a2:Data.Text.Array.Array
--       -> o2:{v:Int | ((v >= 0) && (v < (alen a2)))}
--       -> cnt:{v:Int | ((v >= 0) && ((v+o1) < (alen a1)) && ((v+o2) < (alen a2)))}
--       -> {v:Bool | ((Prop v) <=> (a1 = a2))}
