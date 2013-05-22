module spec Data.Text where

compareText :: Data.Text.Internal.Text
            -> Data.Text.Internal.Text
            -> Ordering

pack :: s:String
     -> {v:Data.Text.Internal.Text | (len s) = (tlength v)}

unpack :: t:Data.Text.Internal.Text
       -> {v:String | (tlength t) = (len v)}

singleton :: Char
          -> {v:Data.Text.Internal.Text | (tlength v) = 1}

cons :: Char
     -> t:Data.Text.Internal.Text
     -> {v:Data.Text.Internal.Text | (tlength v) = (1 + (tlength t))}

snoc :: t:Data.Text.Internal.Text
     -> Char
     -> {v:Data.Text.Internal.Text | (tlength v) = (1 + (tlength t))}

append :: t1:Data.Text.Internal.Text
       -> t2:Data.Text.Internal.Text
       -> {v:Data.Text.Internal.Text | (tlength v) = ((tlength t1) + (tlength t2))}

head :: {v:Data.Text.Internal.Text | (tlength v) > 0}
     -> Char

last :: {v:Data.Text.Internal.Text | (tlength v) > 0}
     -> Char

tail :: t:{v:Data.Text.Internal.Text | (tlength v) > 0}
     -> {v:Data.Text.Internal.Text | ((tlength v) = ((tlength t) - 1))}

init :: t:{v:Data.Text.Internal.Text | (tlength v) > 0}
     -> {v:Data.Text.Internal.Text | ((tlength v) = ((tlength t) - 1))}

null :: t:Data.Text.Internal.Text
     -> {v:Bool | ((Prop v) <=> ((tlength t) = 0))}

isSingleton :: t:Data.Text.Internal.Text
            -> {v:Bool | ((Prop v) <=> ((tlength t) = 1))}

length :: t:Data.Text.Internal.Text
       -> {v:Int | v = (tlength t)}

compareLength :: t:Data.Text.Internal.Text
              -> l:Int
              -> {v:Ordering | ((v = GHC.Types.EQ) <=> ((tlength t) = l))}

map :: (Char -> Char)
    -> t:Data.Text.Internal.Text
    -> {v:Data.Text.Internal.Text | (tlength t) = (tlength v)}

intercalate :: Data.Text.Internal.Text
            -> ts:[Data.Text.Internal.Text]
            -> {v:Data.Text.Internal.Text | (tlength v) >= (sum_tlengths ts)}

intersperse :: Char
            -> t:Data.Text.Internal.Text
            -> {v:Data.Text.Internal.Text | (tlength v) > (tlength t)}

reverse :: t:Data.Text.Internal.Text
        -> {v:Data.Text.Internal.Text | (tlength v) = (tlength t)}

replace :: {v:Data.Text.Internal.Text | (tlength v) > 0}
        -> Data.Text.Internal.Text
        -> Data.Text.Internal.Text
        -> Data.Text.Internal.Text

toCaseFold :: t:Data.Text.Internal.Text
           -> {v:Data.Text.Internal.Text | (tlength v) >= (tlength t)}

toLower :: t:Data.Text.Internal.Text
        -> {v:Data.Text.Internal.Text | (tlength v) >= (tlength t)}

toUpper :: t:Data.Text.Internal.Text
        -> {v:Data.Text.Internal.Text | (tlength v) >= (tlength t)}

justifyLeft :: i:Int
            -> Char
            -> t:Data.Text.Internal.Text
            -> {v:Data.Text.Internal.Text | (Max (tlength v) i (tlength t))}

justifyRight :: i:Int
             -> Char
             -> t:Data.Text.Internal.Text
             -> {v:Data.Text.Internal.Text | (Max (tlength v) i (tlength t))}

center :: i:Int
       -> Char
       -> t:Data.Text.Internal.Text
       -> {v:Data.Text.Internal.Text | (Max (tlength v) i (tlength t))}

foldl1 :: (Char -> Char -> Char)
       -> {v:Data.Text.Internal.Text | (tlength v) > 0}
       -> Char

foldl1' :: (Char -> Char -> Char)
        -> {v:Data.Text.Internal.Text | (tlength v) > 0}
        -> Char

foldr1 :: (Char -> Char -> Char)
       -> {v:Data.Text.Internal.Text | (tlength v) > 0}
       -> Char

concat :: ts:[Data.Text.Internal.Text]
       -> {v:Data.Text.Internal.Text | (tlength v) = (sum_tlengths ts)}

mapAccumL :: (a -> Char -> (a,Char))
          -> a
          -> t:Data.Text.Internal.Text
          -> (a, {v:Data.Text.Internal.Text | (tlength v) = (tlength t)})

mapAccumR :: (a -> Char -> (a,Char))
          -> a
          -> t:Data.Text.Internal.Text
          -> (a, {v:Data.Text.Internal.Text | (tlength v) = (tlength t)})

replicate :: n:{v:Int | v >= 0}
          -> t:Data.Text.Internal.Text
          -> {v:Data.Text.Internal.Text | ((n = 0) ? ((tlength v) = 0)
                                                   : ((tlength v) >= (tlength t)))}

replicateChar :: n:Int
              -> Char
              -> {v:Data.Text.Internal.Text | (tlength v) = n}

take :: n:{v:Int | v >= 0}
     -> t:Data.Text.Internal.Text
     -> {v:Data.Text.Internal.Text | (Min (tlength v) (tlength t) n)}

drop :: n:{v:Int | v >= 0}
     -> t:Data.Text.Internal.Text
     -> {v:Data.Text.Internal.Text | ((tlength v) = (((tlength t) <= n) ? 0 : ((tlength t) - n)))}

takeWhile :: (Char -> Bool)
          -> t:Data.Text.Internal.Text
          -> {v:Data.Text.Internal.Text | (tlength v) <= (tlength t)}

dropWhile :: (Char -> Bool)
          -> t:Data.Text.Internal.Text
          -> {v:Data.Text.Internal.Text | (tlength v) <= (tlength t)}

dropWhileEnd :: (Char -> Bool)
             -> t:Data.Text.Internal.Text
             -> {v:Data.Text.Internal.Text | (tlength v) <= (tlength t)}

dropAround :: (Char -> Bool)
           -> t:Data.Text.Internal.Text
           -> {v:Data.Text.Internal.Text | (tlength v) <= (tlength t)}

stripStart :: t:Data.Text.Internal.Text
           -> {v:Data.Text.Internal.Text | (tlength v) <= (tlength t)}

stripEnd :: t:Data.Text.Internal.Text
         -> {v:Data.Text.Internal.Text | (tlength v) <= (tlength t)}

strip :: t:Data.Text.Internal.Text
      -> {v:Data.Text.Internal.Text | (tlength v) <= (tlength t)}

splitAt :: n:{v:Int | v >= 0}
        -> t:Data.Text.Internal.Text
        -> (Data.Text.Internal.Text, Data.Text.Internal.Text)<{\x y ->
             ((Min (tlength x) (tlength t) n)
              && ((tlength y) = ((tlength t) - (tlength x))))}>

-- FIXME: this `ix' business is a hack to get around our lack of uniqification in abstract refinment binders
inits :: t:Data.Text.Internal.Text
      -> [{v:Data.Text.Internal.Text | (tlength v) <= (tlength t)}]<{\ix iy ->
          ((tlength ix) < (tlength iy))}>

tails :: t:Data.Text.Internal.Text
      -> [{v:Data.Text.Internal.Text | (tlength v) <= (tlength t)}]<{\x y -> (tlength x) > (tlength y)}>

splitOn :: {v:Data.Text.Internal.Text | (tlength v) > 0}
        -> Data.Text.Internal.Text
        -> [Data.Text.Internal.Text]

chunksOf :: k:{v:Int | v >= 0}
         -> t:Data.Text.Internal.Text
         -> [{v:Data.Text.Internal.Text | (tlength v) <= k}]

partition :: (Char -> Bool)
          -> t:Data.Text.Internal.Text
          -> ( {v:Data.Text.Internal.Text | (tlength v) <= (tlength t)}
             , {v:Data.Text.Internal.Text | (tlength v) <= (tlength t)})

filter :: (Char -> Bool)
       -> t:Data.Text.Internal.Text
       -> {v:Data.Text.Internal.Text | (tlength v) <= (tlength t)}

breakOn :: pat:{v:Data.Text.Internal.Text | (tlength v) > 0}
        -> src:Data.Text.Internal.Text
        -> (Data.Text.Internal.Text, Data.Text.Internal.Text)

breakOnEnd :: pat:{v:Data.Text.Internal.Text | (tlength v) > 0}
           -> src:Data.Text.Internal.Text
           -> (Data.Text.Internal.Text, Data.Text.Internal.Text)

breakOnAll :: pat:{v:Data.Text.Internal.Text | (tlength v) > 0}
           -> src:Data.Text.Internal.Text
           -> [(Data.Text.Internal.Text, Data.Text.Internal.Text)]

index :: t:Data.Text.Internal.Text
      -> {v:Int | v < (tlength t)}
      -> Char

findIndex :: (Char -> Bool)
          -> t:Data.Text.Internal.Text
          -> {v:Maybe {v0:Int | ((isJust v) => (Btwn v0 0 (tlength t)))} | true}

count :: {v:Data.Text.Internal.Text | (tlength v) > 0}
      -> Data.Text.Internal.Text
      -> Int

isPrefixOf :: t1:Data.Text.Internal.Text
           -> t2:Data.Text.Internal.Text
           -> {v:Bool | ((Prop v) => ((tlen t1) <= (tlen t2)))}

isSuffixOf :: t1:Data.Text.Internal.Text
           -> t2:Data.Text.Internal.Text
           -> {v:Bool | ((Prop v) => ((tlen t1) <= (tlen t2)))}
