module spec Data.ByteString.Lazy where

assume empty :: { bs : Data.ByteString.Lazy.ByteString | bllen bs == 0 }

assume singleton
    :: Char -> { bs : Data.ByteString.Lazy.ByteString | bllen bs == 1 }

assume pack
    :: w8s : [Char]
    -> { bs : Data.ByteString.ByteString | bllen bs == len w8s }

assume unpack
    :: bs : Data.ByteString.Lazy.ByteString
    -> { w8s : [Char] | len w8s == bllen bs }

assume fromStrict
    :: i : Data.ByteString.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bslen i }

assume toStrict
    :: i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bllen i }

assume fromChunks
    :: i : [Data.ByteString.ByteString]
    -> { o : Data.ByteString.Lazy.ByteString | len i == 0 <=> bllen o == 0 }

assume toChunks
    :: i : Data.ByteString.Lazy.ByteString
    -> { os : [{ o : Data.ByteString.ByteString | bslen o <= bllen i}] | len os == 0 <=> bllen i == 0 }

assume cons
    :: Char
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i + 1 }

assume snoc
    :: i : Data.ByteString.Lazy.ByteString
    -> Char
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i + 1 }

assume append
    :: l : Data.ByteString.Lazy.ByteString
    -> r : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen l + bllen r }

head
    :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> Char

assume uncons
    :: i : Data.ByteString.Lazy.ByteString
    -> Maybe (Char, { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i - 1 })

assume unsnoc
    :: i : Data.ByteString.Lazy.ByteString
    -> Maybe ({ o : Data.ByteString.Lazy.ByteString | bllen o == bllen i - 1 }, Char)

last
    :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> Char

tail
    :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> Char

init
    :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> Char

assume null
    :: bs : Data.ByteString.Lazy.ByteString
    -> { b : Bool | b <=> bllen bs == 0 }

assume length
    :: bs : Data.ByteString.Lazy.ByteString -> { n : Data.Int.Int64 | bllen bs == n }

assume map
    :: (Char -> Char)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume reverse
    :: i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume intersperse
    :: Char
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | (bllen i == 0 <=> bllen o == 0) && (1 <= bllen i <=> bllen o == 2 * bllen i - 1) }

assume intercalate
    :: l : Data.ByteString.Lazy.ByteString
    -> rs : [Data.ByteString.Lazy.ByteString]
    -> { o : Data.ByteString.Lazy.ByteString | len rs == 0 ==> bllen o == 0 }

assume transpose
    :: is : [Data.ByteString.Lazy.ByteString]
    -> { os : [{ bs : Data.ByteString.Lazy.ByteString | bllen bs <= len is }] | len is == 0 ==> len os == 0}

foldl1
    :: (Char -> Char -> Char)
    -> { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> Char

foldl1'
    :: (Char -> Char -> Char)
    -> { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> Char

foldr1
    :: (Char -> Char -> Char)
    -> { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> Char

foldr1'
    :: (Char -> Char -> Char)
    -> { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> Char

assume concat
    :: is : [Data.ByteString.Lazy.ByteString]
    -> { o : Data.ByteString.Lazy.ByteString | len is == 0 ==> bllen o }

assume concatMap
    :: (Char -> Data.ByteString.Lazy.ByteString)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen i == 0 ==> bllen o == 0 }

assume any :: (Char -> Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> { b : Bool | bllen bs == 0 ==> not b }

assume all :: (Char -> Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> { b : Bool | bllen bs == 0 ==> b }

maximum :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs } -> Char

minimum :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs } -> Char

assume scanl
    :: (Char -> Char -> Char)
    -> Char
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume scanl1
    :: (Char -> Char -> Char)
    -> i : { i : Data.ByteString.Lazy.ByteString | 1 <= bllen i }
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume scanr
    :: (Char -> Char -> Char)
    -> Char
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume scanr1
    :: (Char -> Char -> Char)
    -> i : { i : Data.ByteString.Lazy.ByteString | 1 <= bllen i }
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume mapAccumL
    :: (acc -> Char -> (acc, Char))
    -> acc
    -> i : Data.ByteString.Lazy.ByteString
    -> (acc, { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i })

assume mapAccumR
    :: (acc -> Char -> (acc, Char))
    -> acc
    -> i : Data.ByteString.Lazy.ByteString
    -> (acc, { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i })

assume replicate
    :: n : Data.Int.Int64
    -> Char
    -> { bs : Data.ByteString.Lazy.ByteString | bllen bs == n }

assume unfoldrN
    :: n : Int
    -> (a -> Maybe (Char, a))
    -> a
    -> ({ bs : Data.ByteString.Lazy.ByteString | bllen bs <= n }, Maybe a)

assume take
    :: n : Data.Int.Int64
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | (n <= 0 ==> bllen o == 0) &&
                                               ((0 <= n && n <= bllen i) <=> bllen o == n) &&
                                               (bllen i <= n <=> bllen o = bllen i) }

assume drop
    :: n : Data.Int.Int64
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | (n <= 0 <=> bllen o == bllen i) &&
                                               ((0 <= n && n <= bllen i) <=> bllen o == bllen i - n) &&
                                               (bllen i <= n <=> bllen o == 0) }

assume splitAt
    :: n : Data.Int.Int64
    -> i : Data.ByteString.Lazy.ByteString
    -> ( { l : Data.ByteString.Lazy.ByteString | (n <= 0 <=> bllen l == 0) &&
                                                 ((0 <= n && n <= bllen i) <=> bllen l == n) &&
                                                 (bllen i <= n <=> bllen l == bllen i) }
       , { r : Data.ByteString.Lazy.ByteString | (n <= 0 <=> bllen r == bllen i) &&
                                                 ((0 <= n && n <= bllen i) <=> bllen r == bllen i - n) &&
                                                 (bllen i <= n <=> bllen r == 0) }
       )

assume takeWhile
    :: (Char -> Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }

assume dropWhile
    :: (Char -> Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }

assume span
    :: (Char -> Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> ( { l : Data.ByteString.Lazy.ByteString | bllen l <= bllen i }
       , { r : Data.ByteString.Lazy.ByteString | bllen r <= bllen i }
       )

assume spanEnd
    :: (Char -> Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> ( { l : Data.ByteString.Lazy.ByteString | bllen l <= bllen i }
       , { r : Data.ByteString.Lazy.ByteString | bllen r <= bllen i }
       )

assume break
    :: (Char -> Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> ( { l : Data.ByteString.Lazy.ByteString | bllen l <= bllen i }
       , { r : Data.ByteString.Lazy.ByteString | bllen r <= bllen i }
       )

assume breakEnd
    :: (Char -> Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> ( { l : Data.ByteString.Lazy.ByteString | bllen l <= bllen i }
       , { r : Data.ByteString.Lazy.ByteString | bllen r <= bllen i }
       )
assume group
    :: i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | 1 <= bllen o && bllen o <= bllen i }]

assume groupBy
    :: (Char -> Char -> Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | 1 <= bllen o && bllen o <= bllen i }]

assume inits
    :: i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }]

assume tails
    :: i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }]

assume split
    :: Char
    -> i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }]

assume splitWith
    :: (Char -> Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }]

assume lines
    :: i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }]

assume words
    :: i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }]

assume unlines
    :: is : [Data.ByteString.Lazy.ByteString]
    -> { o : Data.ByteString.Lazy.ByteString | (len is == 0 <=> bllen o == 0) && bllen o >= len is }

assume unwords
    :: is : [Data.ByteString.Lazy.ByteString]
    -> { o : Data.ByteString.Lazy.ByteString | (len is == 0 ==> bllen o == 0) && (1 <= len is ==> bllen o >= len is - 1) }

assume isPrefixOf
    :: l : Data.ByteString.Lazy.ByteString
    -> r : Data.ByteString.Lazy.ByteString
    -> { b : Bool | bllen l >= bllen r ==> not b }

assume isSuffixOf
    :: l : Data.ByteString.Lazy.ByteString
    -> r : Data.ByteString.Lazy.ByteString
    -> { b : Bool | bllen l >= bllen r ==> not b }

assume isInfixOf
    :: l : Data.ByteString.Lazy.ByteString
    -> r : Data.ByteString.Lazy.ByteString
    -> { b : Bool | bllen l >= bllen r ==> not b }

assume breakSubstring
    :: il : Data.ByteString.Lazy.ByteString
    -> ir : Data.ByteString.Lazy.ByteString
    -> ( { ol : Data.ByteString.Lazy.ByteString | bllen ol <= bllen ir && (bllen il > bllen ir ==> bllen ol == bllen ir)}
       , { or : Data.ByteString.Lazy.ByteString | bllen or <= bllen ir && (bllen il > bllen ir ==> bllen or == 0) }
       )

assume elem
    :: Char
    -> bs : Data.ByteString.Lazy.ByteString
    -> { b : Bool | bllen b == 0 ==> not b }

assume notElem
    :: Char
    -> bs : Data.ByteString.Lazy.ByteString
    -> { b : Bool | bllen b == 0 ==> b }

assume find
    :: (Char -> Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> Maybe { w8 : Char | bllen bs /= 0 }

assume filter
    :: (Char -> Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }

assume partition
    :: (Char -> Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> ( { l : Data.ByteString.Lazy.ByteString | bllen l <= bllen i }
       , { r : Data.ByteString.Lazy.ByteString | bllen r <= bllen i }
       )

index
    :: bs : Data.ByteString.Lazy.ByteString
    -> { n : Data.Int.Int64 | 0 <= n && n < bllen bs }
    -> Char

assume elemIndex
    :: Char
    -> bs : Data.ByteString.Lazy.ByteString
    -> Maybe { n : Data.Int.Int64 | 0 <= n && n < bllen bs }

assume elemIndices
    :: Char
    -> bs : Data.ByteString.Lazy.ByteString
    -> [{ n : Data.Int.Int64 | 0 <= n && n < bllen bs }]

assume elemIndexEnd
    :: Char
    -> bs : Data.ByteString.Lazy.ByteString
    -> Maybe { n : Data.Int.Int64 | 0 <= n && n < bllen bs }

assume findIndex
    :: (Char -> Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> Maybe { n : Data.Int.Int64 | 0 <= n && n < bllen bs }

assume findIndices
    :: (Char -> Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> [{ n : Data.Int.Int64 | 0 <= n && n < bllen bs }]

assume count
    :: Char
    -> bs : Data.ByteString.Lazy.ByteString
    -> { n : Data.Int.Int64 | 0 <= n && n < bllen bs }

assume zip
    :: l : Data.ByteString.Lazy.ByteString
    -> r : Data.ByteString.Lazy.ByteString
    -> { o : [(Char, Char)] | len o <= bllen l && len o <= bllen r }

assume zipWith
    :: (Char -> Char -> a)
    -> l : Data.ByteString.Lazy.ByteString
    -> r : Data.ByteString.Lazy.ByteString
    -> { o : [a] | len o <= bllen l && len o <= bllen r }

assume unzip
    :: i : [(Char, Char)]
    -> ( { l : Data.ByteString.Lazy.ByteString | bllen l == len i }
       , { r : Data.ByteString.Lazy.ByteString | bllen r == len i }
       )

assume sort
    :: i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume readInt
    :: i : Data.ByteString.Lazy.ByteString
    -> Maybe { p : (Int, { o : Data.ByteString.Lazy.ByteString | bllen o < bllen i}) | bllen i /= 0 }

assume readInteger
    :: i : Data.ByteString.Lazy.ByteString
    -> Maybe { p : (Integer, { o : Data.ByteString.Lazy.ByteString | bllen o < bllen i}) | bllen i /= 0 }

assume copy
    :: i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume hGet
    :: System.IO.Handle
    -> n : { n : Int | 0 <= n }
    -> IO { bs : Data.ByteString.Lazy.ByteString | bllen bs == n || bllen bs == 0 }

assume hGetNonBlocking
    :: System.IO.Handle
    -> n : { n : Int | 0 <= n }
    -> IO { bs : Data.ByteString.Lazy.ByteString | bllen bs <= n }
