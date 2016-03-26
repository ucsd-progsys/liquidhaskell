module spec Data.ByteString where

measure bslen :: Data.ByteString.ByteString -> { n : Int | 0 <= n }

invariant { bs : Data.ByteString.ByteString  | 0 <= bslen bs }

assume empty :: { bs : Data.ByteString.ByteString | bslen bs == 0 }

assume singleton
    :: Data.Word.Word8 -> { bs : Data.ByteString.ByteString | bslen bs == 1 }

assume pack
    :: w8s : [Data.Word.Word8]
    -> { bs : Data.ByteString.ByteString | bslen bs == len w8s }

assume unpack
    :: bs : Data.ByteString.ByteString
    -> { w8s : [Data.Word.Word8] | len w8s == bslen bs }

assume cons
    :: Data.Word.Word8
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i + 1 }

assume snoc
    :: i : Data.ByteString.ByteString
    -> Data.Word.Word8
    -> { o : Data.ByteString.ByteString | bslen o == bslen i + 1 }

assume append
    :: l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen l + bslen r }

head :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> Data.Word.Word8

assume uncons
    :: i : Data.ByteString.ByteString
    -> Maybe (Data.Word.Word8, { o : Data.ByteString.ByteString | bslen o == bslen i - 1 })

assume unsnoc
    :: i : Data.ByteString.ByteString
    -> Maybe ({ o : Data.ByteString.ByteString | bslen o == bslen i - 1 }, Data.Word.Word8)

last :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> Data.Word.Word8

tail :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> Data.Word.Word8

init :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> Data.Word.Word8

assume null
    :: bs : Data.ByteString.ByteString
    -> { b : Bool | Prop b <=> bslen bs == 0 }

assume length :: bs : Data.ByteString.ByteString -> { n : Int | bslen bs == n }

assume map
    :: (Data.Word.Word8 -> Data.Word.Word8)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume reverse
    :: i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume intersperse
    :: Data.Word.Word8
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | (bslen i == 0 <=> bslen o == 0) && (1 <= bslen i <=> bslen o == 2 * bslen i - 1) }

assume intercalate
    :: l : Data.ByteString.ByteString
    -> rs : [Data.ByteString.ByteString]
    -> { o : Data.ByteString.ByteString | len rs == 0 ==> bslen o == 0 }

assume transpose
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

assume concat
    :: is : [Data.ByteString.ByteString]
    -> { o : Data.ByteString.ByteString | len is == 0 ==> bslen o }

assume concatMap
    :: (Data.Word.Word8 -> Data.ByteString.ByteString)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen i == 0 ==> bslen o == 0 }

assume any :: (Data.Word.Word8 -> Bool)
    -> bs : Data.ByteString.ByteString
    -> { b : Bool | bslen bs == 0 ==> not (Prop b) }

assume all :: (Data.Word.Word8 -> Bool)
    -> bs : Data.ByteString.ByteString
    -> { b : Bool | bslen bs == 0 ==> Prop b }

maximum
    :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> Data.Word.Word8

minimum
    :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> Data.Word.Word8

assume scanl
    :: (Data.Word.Word8 -> Data.Word.Word8 -> Data.Word.Word8)
    -> Data.Word.Word8
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume scanl1
    :: (Data.Word.Word8 -> Data.Word.Word8 -> Data.Word.Word8)
    -> i : { i : Data.ByteString.ByteString | 1 <= bslen i }
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume scanr
    :: (Data.Word.Word8 -> Data.Word.Word8 -> Data.Word.Word8)
    -> Data.Word.Word8
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume scanr1
    :: (Data.Word.Word8 -> Data.Word.Word8 -> Data.Word.Word8)
    -> i : { i : Data.ByteString.ByteString | 1 <= bslen i }
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume mapAccumL
    :: (acc -> Data.Word.Word8 -> (acc, Data.Word.Word8))
    -> acc
    -> i : Data.ByteString.ByteString
    -> (acc, { o : Data.ByteString.ByteString | bslen o == bslen i })

assume mapAccumR
    :: (acc -> Data.Word.Word8 -> (acc, Data.Word.Word8))
    -> acc
    -> i : Data.ByteString.ByteString
    -> (acc, { o : Data.ByteString.ByteString | bslen o == bslen i })

assume replicate
    :: n : Int
    -> Data.Word.Word8
    -> { bs : Data.ByteString.ByteString | bslen bs == n }

assume unfoldrN
    :: n : Int
    -> (a -> Maybe (Data.Word.Word8, a))
    -> a
    -> ({ bs : Data.ByteString.ByteString | bslen bs <= n }, Maybe a)

assume take
    :: n : Int
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | (n <= 0 <=> bslen o == 0) &&
                                          ((0 <= n && n <= bslen i) <=> bslen o == n) &&
                                          (bslen i <= n <=> bslen o = bslen i) }

assume drop
    :: n : Int
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | (n <= 0 <=> bslen o == bslen i) &&
                                          ((0 <= n && n <= bslen i) <=> bslen o == bslen i - n) &&
                                          (bslen i <= n <=> bslen o == 0) }

assume splitAt
    :: n : Int
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | (n <= 0 <=> bslen l == 0) &&
                                            ((0 <= n && n <= bslen i) <=> bslen l == n) &&
                                            (bslen i <= n <=> bslen l == bslen i) }
       , { r : Data.ByteString.ByteString | (n <= 0 <=> bslen r == bslen i) &&
                                            ((0 <= n && n <= bslen i) <=> bslen r == bslen i - n) &&
                                            (bslen i <= n <=> bslen r == 0) }
       )

assume takeWhile
    :: (Data.Word.Word8 -> Bool)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o <= bslen i }

assume dropWhile
    :: (Data.Word.Word8 -> Bool)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o <= bslen i }

assume span
    :: (Data.Word.Word8 -> Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

assume spanEnd
    :: (Data.Word.Word8 -> Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

assume break
    :: (Data.Word.Word8 -> Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

assume breakEnd
    :: (Data.Word.Word8 -> Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

assume group
    :: i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | 1 <= bslen o && bslen o <= bslen i }]

assume groupBy
    :: (Data.Word.Word8 -> Data.Word.Word8 -> Bool)
    -> i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | 1 <= bslen o && bslen o <= bslen i }]

assume inits
    :: i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | bslen o <= bslen i }]

assume tails
    :: i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | bslen o <= bslen i }]

assume split
    :: Data.Word.Word8
    -> i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | bslen o <= bslen i }]

assume splitWith
    :: (Data.Word.Word8 -> Bool)
    -> i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | bslen o <= bslen i }]

assume isPrefixOf
    :: l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { b : Bool | bslen l >= bslen r ==> not (Prop b) }

assume isSuffixOf
    :: l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { b : Bool | bslen l > bslen r ==> not (Prop b) }

assume isInfixOf
    :: l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { b : Bool | bslen l > bslen r ==> not (Prop b) }

assume breakSubstring
    :: il : Data.ByteString.ByteString
    -> ir : Data.ByteString.ByteString
    -> ( { ol : Data.ByteString.ByteString | bslen ol <= bslen ir && (bslen il > bslen ir ==> bslen ol == bslen ir)}
       , { or : Data.ByteString.ByteString | bslen or <= bslen ir && (bslen il > bslen ir ==> bslen or == 0) }
       )

assume elem
    :: Data.Word.Word8
    -> bs : Data.ByteString.ByteString
    -> { b : Bool | bslen b == 0 ==> not (Prop b) }

assume notElem
    :: Data.Word.Word8
    -> bs : Data.ByteString.ByteString
    -> { b : Bool | bslen b == 0 ==> Prop b }

assume find
    :: (Data.Word.Word8 -> Bool)
    -> bs : Data.ByteString.ByteString
    -> Maybe { w8 : Data.Word.Word8 | bslen bs /= 0 }

assume filter
    :: (Data.Word.Word8 -> Bool)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o <= bslen i }

assume partition
    :: (Data.Word.Word8 -> Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

index
    :: bs : Data.ByteString.ByteString
    -> { n : Int | 0 <= n && n < bslen bs }
    -> Data.Word.Word8

assume elemIndex
    :: Data.Word.Word8
    -> bs : Data.ByteString.ByteString
    -> Maybe { n : Int | 0 <= n && n < bslen bs }

assume elemIndices
    :: Data.Word.Word8
    -> bs : Data.ByteString.ByteString
    -> [{ n : Int | 0 <= n && n < bslen bs }]

assume elemIndexEnd
    :: Data.Word.Word8
    -> bs : Data.ByteString.ByteString
    -> Maybe { n : Int | 0 <= n && n < bslen bs }

assume findIndex
    :: (Data.Word.Word8 -> Bool)
    -> bs : Data.ByteString.ByteString
    -> Maybe { n : Int | 0 <= n && n < bslen bs }

assume findIndices
    :: (Data.Word.Word8 -> Bool)
    -> bs : Data.ByteString.ByteString
    -> [{ n : Int | 0 <= n && n < bslen bs }]

assume count
    :: Data.Word.Word8
    -> bs : Data.ByteString.ByteString
    -> { n : Int | 0 <= n && n < bslen bs }

assume zip
    :: l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { o : [(Data.Word.Word8, Data.Word.Word8)] | len o <= bslen l && len o <= bslen r }

assume zipWith
    :: (Data.Word.Word8 -> Data.Word.Word8 -> a)
    -> l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { o : [a] | len o <= bslen l && len o <= bslen r }

assume unzip
    :: i : [(Data.Word.Word8, Data.Word.Word8)]
    -> ( { l : Data.ByteString.ByteString | bslen l == len i }
       , { r : Data.ByteString.ByteString | bslen r == len i }
       )

assume sort
    :: i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume copy
    :: i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume hGet
    :: System.IO.Handle
    -> n : { n : Int | 0 <= n }
    -> IO { bs : Data.ByteString.ByteString | bslen bs == n || bslen bs == 0 }

assume hGetSome
    :: System.IO.Handle
    -> n : { n : Int | 0 <= n }
    -> IO { bs : Data.ByteString.ByteString | bslen bs <= n }

assume hGetNonBlocking
    :: System.IO.Handle
    -> n : { n : Int | 0 <= n }
    -> IO { bs : Data.ByteString.ByteString | bslen bs <= n }
