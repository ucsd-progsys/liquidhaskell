module spec Data.ByteString where

measure bslen :: Data.ByteString.ByteString -> { n : Int | 0 <= n }

invariant { bs : Data.ByteString.ByteString  | 0 <= bslen bs }

empty :: { bs : Data.ByteString.ByteString | bslen bs == 0 }

singleton
    :: Data.Word.Word8 -> { bs : Data.ByteString.ByteString | bslen bs == 1 }

pack
    :: w8s : [Data.Word.Word8]
    -> { bs : Data.ByteString.ByteString | bslen bs == len w8s }

unpack
    :: bs : Data.ByteString.ByteString
    -> { w8s : [Data.Word.Word8] | len w8s == bslen bs }

cons
    :: Data.Word.Word8
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i + 1 }

snoc
    :: i : Data.ByteString.ByteString
    -> Data.Word.Word8
    -> { o : Data.ByteString.ByteString | bslen o == bslen i + 1 }

append
    :: l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen l + bslen r }

head :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> Data.Word.Word8

unsnoc
    :: i : Data.ByteString.ByteString
    -> Maybe ({ o : Data.ByteString.ByteString | bslen o == bslen i - 1 }, Data.Word.Word8)

last :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> Data.Word.Word8

tail :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> Data.Word.Word8

init :: {i:Data.ByteString.ByteString | 1 <= bslen i } 
     -> {o:Data.ByteString.ByteString | bslen o == bslen i - 1 }

null
    :: bs : Data.ByteString.ByteString
    -> { b : Bool | Prop b <=> bslen bs == 0 }

length :: bs : Data.ByteString.ByteString -> { n : Int | bslen bs == n }

map
    :: (Data.Word.Word8 -> Data.Word.Word8)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

reverse
    :: i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

intersperse
    :: Data.Word.Word8
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | (bslen i == 0 <=> bslen o == 0) && (1 <= bslen i <=> bslen o == 2 * bslen i - 1) }

intercalate
    :: l : Data.ByteString.ByteString
    -> rs : [Data.ByteString.ByteString]
    -> { o : Data.ByteString.ByteString | len rs == 0 ==> bslen o == 0 }

transpose
    :: is : [Data.ByteString.ByteString]
    -> { os : [{ bs : Data.ByteString.ByteString | bslen bs <= len is }] | len is == 0 ==> len os == 0}

foldl1
    :: (Data.Word.Word8 -> Data.Word.Word8 -> Data.Word.Word8)
    -> { bs : Data.ByteString.ByteString | 1 <= bslen bs }
    -> Data.Word.Word8

foldl1'
    :: (Data.Word.Word8 -> Data.Word.Word8 -> Data.Word.Word8)
    -> { bs : Data.ByteString.ByteString | 1 <= bslen bs }
    -> Data.Word.Word8

foldr1
    :: (Data.Word.Word8 -> Data.Word.Word8 -> Data.Word.Word8)
    -> { bs : Data.ByteString.ByteString | 1 <= bslen bs }
    -> Data.Word.Word8

foldr1'
    :: (Data.Word.Word8 -> Data.Word.Word8 -> Data.Word.Word8)
    -> { bs : Data.ByteString.ByteString | 1 <= bslen bs }
    -> Data.Word.Word8

concat
    :: is : [Data.ByteString.ByteString]
    -> { o : Data.ByteString.ByteString | len is == 0 ==> bslen o }

concatMap
    :: (Data.Word.Word8 -> Data.ByteString.ByteString)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen i == 0 ==> bslen o == 0 }

any :: (Data.Word.Word8 -> Bool)
    -> bs : Data.ByteString.ByteString
    -> { b : Bool | bslen bs == 0 ==> not (Prop b) }

all :: (Data.Word.Word8 -> Bool)
    -> bs : Data.ByteString.ByteString
    -> { b : Bool | bslen bs == 0 ==> Prop b }

maximum
    :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> Data.Word.Word8

minimum
    :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> Data.Word.Word8

scanl
    :: (Data.Word.Word8 -> Data.Word.Word8 -> Data.Word.Word8)
    -> Data.Word.Word8
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

scanl1
    :: (Data.Word.Word8 -> Data.Word.Word8 -> Data.Word.Word8)
    -> i : { i : Data.ByteString.ByteString | 1 <= bslen i }
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

scanr
    :: (Data.Word.Word8 -> Data.Word.Word8 -> Data.Word.Word8)
    -> Data.Word.Word8
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

scanr1
    :: (Data.Word.Word8 -> Data.Word.Word8 -> Data.Word.Word8)
    -> i : { i : Data.ByteString.ByteString | 1 <= bslen i }
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

mapAccumL
    :: (acc -> Data.Word.Word8 -> (acc, Data.Word.Word8))
    -> acc
    -> i : Data.ByteString.ByteString
    -> (acc, { o : Data.ByteString.ByteString | bslen o == bslen i })

mapAccumR
    :: (acc -> Data.Word.Word8 -> (acc, Data.Word.Word8))
    -> acc
    -> i : Data.ByteString.ByteString
    -> (acc, { o : Data.ByteString.ByteString | bslen o == bslen i })

replicate
    :: n : Int
    -> Data.Word.Word8
    -> { bs : Data.ByteString.ByteString | bslen bs == n }

unfoldrN
    :: n : Int
    -> (a -> Maybe (Data.Word.Word8, a))
    -> a
    -> ({ bs : Data.ByteString.ByteString | bslen bs <= n }, Maybe a)

take
    :: n : Int
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | (n <= 0 <=> bslen o == 0) &&
                                          ((0 <= n && n <= bslen i) <=> bslen o == n) &&
                                          (bslen i <= n <=> bslen o = bslen i) }

drop
    :: n : Int
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | (n <= 0 <=> bslen o == bslen i) &&
                                          ((0 <= n && n <= bslen i) <=> bslen o == bslen i - n) &&
                                          (bslen i <= n <=> bslen o == 0) }

splitAt
    :: n : Int
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | (n <= 0 <=> bslen l == 0) &&
                                            ((0 <= n && n <= bslen i) <=> bslen l == n) &&
                                            (bslen i <= n <=> bslen l == bslen i) }
       , { r : Data.ByteString.ByteString | (n <= 0 <=> bslen r == bslen i) &&
                                            ((0 <= n && n <= bslen i) <=> bslen r == bslen i - n) &&
                                            (bslen i <= n <=> bslen r == 0) }
       )

takeWhile
    :: (Data.Word.Word8 -> Bool)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o <= bslen i }

dropWhile
    :: (Data.Word.Word8 -> Bool)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o <= bslen i }

span
    :: (Data.Word.Word8 -> Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

spanEnd
    :: (Data.Word.Word8 -> Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

break
    :: (Data.Word.Word8 -> Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

breakEnd
    :: (Data.Word.Word8 -> Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

group
    :: i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | 1 <= bslen o && bslen o <= bslen i }]

groupBy
    :: (Data.Word.Word8 -> Data.Word.Word8 -> Bool)
    -> i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | 1 <= bslen o && bslen o <= bslen i }]

inits
    :: i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | bslen o <= bslen i }]

tails
    :: i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | bslen o <= bslen i }]

split
    :: Data.Word.Word8
    -> i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | bslen o <= bslen i }]

splitWith
    :: (Data.Word.Word8 -> Bool)
    -> i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | bslen o <= bslen i }]

isPrefixOf
    :: l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { b : Bool | bslen l >= bslen r ==> not (Prop b) }

isSuffixOf
    :: l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { b : Bool | bslen l > bslen r ==> not (Prop b) }

isInfixOf
    :: l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { b : Bool | bslen l > bslen r ==> not (Prop b) }

breakSubstring
    :: il : Data.ByteString.ByteString
    -> ir : Data.ByteString.ByteString
    -> ( { ol : Data.ByteString.ByteString | bslen ol <= bslen ir && (bslen il > bslen ir ==> bslen ol == bslen ir)}
       , { or : Data.ByteString.ByteString | bslen or <= bslen ir && (bslen il > bslen ir ==> bslen or == 0) }
       )

elem
    :: Data.Word.Word8
    -> bs : Data.ByteString.ByteString
    -> { b : Bool | bslen b == 0 ==> not (Prop b) }

notElem
    :: Data.Word.Word8
    -> bs : Data.ByteString.ByteString
    -> { b : Bool | bslen b == 0 ==> Prop b }

find
    :: (Data.Word.Word8 -> Bool)
    -> bs : Data.ByteString.ByteString
    -> Maybe { w8 : Data.Word.Word8 | bslen bs /= 0 }

filter
    :: (Data.Word.Word8 -> Bool)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o <= bslen i }

partition
    :: (Data.Word.Word8 -> Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

index
    :: bs : Data.ByteString.ByteString
    -> { n : Int | 0 <= n && n < bslen bs }
    -> Data.Word.Word8

elemIndex
    :: Data.Word.Word8
    -> bs : Data.ByteString.ByteString
    -> Maybe { n : Int | 0 <= n && n < bslen bs }

elemIndices
    :: Data.Word.Word8
    -> bs : Data.ByteString.ByteString
    -> [{ n : Int | 0 <= n && n < bslen bs }]

elemIndexEnd
    :: Data.Word.Word8
    -> bs : Data.ByteString.ByteString
    -> Maybe { n : Int | 0 <= n && n < bslen bs }

findIndex
    :: (Data.Word.Word8 -> Bool)
    -> bs : Data.ByteString.ByteString
    -> Maybe { n : Int | 0 <= n && n < bslen bs }

findIndices
    :: (Data.Word.Word8 -> Bool)
    -> bs : Data.ByteString.ByteString
    -> [{ n : Int | 0 <= n && n < bslen bs }]

count
    :: Data.Word.Word8
    -> bs : Data.ByteString.ByteString
    -> { n : Int | 0 <= n && n < bslen bs }

zip
    :: l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { o : [(Data.Word.Word8, Data.Word.Word8)] | len o <= bslen l && len o <= bslen r }

zipWith
    :: (Data.Word.Word8 -> Data.Word.Word8 -> a)
    -> l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { o : [a] | len o <= bslen l && len o <= bslen r }

unzip
    :: i : [(Data.Word.Word8, Data.Word.Word8)]
    -> ( { l : Data.ByteString.ByteString | bslen l == len i }
       , { r : Data.ByteString.ByteString | bslen r == len i }
       )

sort
    :: i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

copy
    :: i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

hGet
    :: System.IO.Handle
    -> n : { n : Int | 0 <= n }
    -> IO { bs : Data.ByteString.ByteString | bslen bs == n || bslen bs == 0 }

hGetSome
    :: System.IO.Handle
    -> n : { n : Int | 0 <= n }
    -> IO { bs : Data.ByteString.ByteString | bslen bs <= n }

hGetNonBlocking
    :: System.IO.Handle
    -> n : { n : Int | 0 <= n }
    -> IO { bs : Data.ByteString.ByteString | bslen bs <= n }

uncons
    :: i : Data.ByteString.ByteString
    -> Maybe (Data.Word.Word8, { o : Data.ByteString.ByteString | bslen o == bslen i - 1 })
