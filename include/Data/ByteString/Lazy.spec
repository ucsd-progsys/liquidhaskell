module spec Data.ByteString.Lazy where

import Data.String

measure bllen :: Data.ByteString.Lazy.ByteString -> { n : Data.Int.Int64 | 0 <= n }

invariant { bs : Data.ByteString.Lazy.ByteString | 0 <= bllen bs }

invariant { bs : Data.ByteString.Lazy.ByteString | bllen bs == stringlen bs }

assume empty :: { bs : Data.ByteString.Lazy.ByteString | bllen bs == 0 }

assume singleton
    :: Data.Word.Word8 -> { bs : Data.ByteString.Lazy.ByteString | bllen bs == 1 }

assume pack
    :: w8s : [Data.Word.Word8]
    -> { bs : Data.ByteString.ByteString | bllen bs == len w8s }

assume unpack
    :: bs : Data.ByteString.Lazy.ByteString
    -> { w8s : [Data.Word.Word8] | len w8s == bllen bs }

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
    :: Data.Word.Word8
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i + 1 }

assume snoc
    :: i : Data.ByteString.Lazy.ByteString
    -> Data.Word.Word8
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i + 1 }

assume append
    :: l : Data.ByteString.Lazy.ByteString
    -> r : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen l + bllen r }

head
    :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> Data.Word.Word8

assume uncons
    :: i : Data.ByteString.Lazy.ByteString
    -> Maybe (Data.Word.Word8, { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i - 1 })

assume unsnoc
    :: i : Data.ByteString.Lazy.ByteString
    -> Maybe ({ o : Data.ByteString.Lazy.ByteString | bllen o == bllen i - 1 }, Data.Word.Word8)

last
    :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> Data.Word.Word8

tail
    :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> Data.Word.Word8

init
    :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> Data.Word.Word8

assume null
    :: bs : Data.ByteString.Lazy.ByteString
    -> { b : Bool | b <=> bllen bs == 0 }

assume length
    :: bs : Data.ByteString.Lazy.ByteString -> { n : Data.Int.Int64 | bllen bs == n }

assume map
    :: (Data.Word.Word8 -> Data.Word.Word8)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume reverse
    :: i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume intersperse
    :: Data.Word.Word8
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
    :: (Data.Word.Word8 -> Data.Word.Word8 -> Data.Word.Word8)
    -> { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> Data.Word.Word8

foldl1'
    :: (Data.Word.Word8 -> Data.Word.Word8 -> Data.Word.Word8)
    -> { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> Data.Word.Word8

foldr1
    :: (Data.Word.Word8 -> Data.Word.Word8 -> Data.Word.Word8)
    -> { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> Data.Word.Word8

assume concat
    :: is : [Data.ByteString.Lazy.ByteString]
    -> { o : Data.ByteString.Lazy.ByteString | len is == 0 ==> bllen o }

assume concatMap
    :: (Data.Word.Word8 -> Data.ByteString.Lazy.ByteString)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen i == 0 ==> bllen o == 0 }

assume any :: (Data.Word.Word8 -> Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> { b : Bool | bllen bs == 0 ==> not b }

assume all :: (Data.Word.Word8 -> Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> { b : Bool | bllen bs == 0 ==> b }

maximum :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs } -> Data.Word.Word8

minimum :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs } -> Data.Word.Word8

assume scanl
    :: (Data.Word.Word8 -> Data.Word.Word8 -> Data.Word.Word8)
    -> Data.Word.Word8
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume mapAccumL
    :: (acc -> Data.Word.Word8 -> (acc, Data.Word.Word8))
    -> acc
    -> i : Data.ByteString.Lazy.ByteString
    -> (acc, { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i })

assume mapAccumR
    :: (acc -> Data.Word.Word8 -> (acc, Data.Word.Word8))
    -> acc
    -> i : Data.ByteString.Lazy.ByteString
    -> (acc, { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i })

assume replicate
    :: n : Data.Int.Int64
    -> Data.Word.Word8
    -> { bs : Data.ByteString.Lazy.ByteString | bllen bs == n }

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
    :: (Data.Word.Word8 -> Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }

assume dropWhile
    :: (Data.Word.Word8 -> Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }

assume span
    :: (Data.Word.Word8 -> Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> ( { l : Data.ByteString.Lazy.ByteString | bllen l <= bllen i }
       , { r : Data.ByteString.Lazy.ByteString | bllen r <= bllen i }
       )

assume break
    :: (Data.Word.Word8 -> Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> ( { l : Data.ByteString.Lazy.ByteString | bllen l <= bllen i }
       , { r : Data.ByteString.Lazy.ByteString | bllen r <= bllen i }
       )

assume group
    :: i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | 1 <= bllen o && bllen o <= bllen i }]

assume groupBy
    :: (Data.Word.Word8 -> Data.Word.Word8 -> Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | 1 <= bllen o && bllen o <= bllen i }]

assume inits
    :: i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }]

assume tails
    :: i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }]

assume split
    :: Data.Word.Word8
    -> i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }]

assume splitWith
    :: (Data.Word.Word8 -> Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }]

assume isPrefixOf
    :: l : Data.ByteString.Lazy.ByteString
    -> r : Data.ByteString.Lazy.ByteString
    -> { b : Bool | bllen l >= bllen r ==> not b }

assume isSuffixOf
    :: l : Data.ByteString.Lazy.ByteString
    -> r : Data.ByteString.Lazy.ByteString
    -> { b : Bool | bllen l >= bllen r ==> not b }

assume elem
    :: Data.Word.Word8
    -> bs : Data.ByteString.Lazy.ByteString
    -> { b : Bool | bllen b == 0 ==> not b }

assume notElem
    :: Data.Word.Word8
    -> bs : Data.ByteString.Lazy.ByteString
    -> { b : Bool | bllen b == 0 ==> b }

assume find
    :: (Data.Word.Word8 -> Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> Maybe { w8 : Data.Word.Word8 | bllen bs /= 0 }

assume filter
    :: (Data.Word.Word8 -> Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }

assume partition
    :: (Data.Word.Word8 -> Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> ( { l : Data.ByteString.Lazy.ByteString | bllen l <= bllen i }
       , { r : Data.ByteString.Lazy.ByteString | bllen r <= bllen i }
       )

index
    :: bs : Data.ByteString.Lazy.ByteString
    -> { n : Data.Int.Int64 | 0 <= n && n < bllen bs }
    -> Data.Word.Word8

assume elemIndex
    :: Data.Word.Word8
    -> bs : Data.ByteString.Lazy.ByteString
    -> Maybe { n : Data.Int.Int64 | 0 <= n && n < bllen bs }

assume elemIndices
    :: Data.Word.Word8
    -> bs : Data.ByteString.Lazy.ByteString
    -> [{ n : Data.Int.Int64 | 0 <= n && n < bllen bs }]

assume elemIndexEnd
    :: Data.Word.Word8
    -> bs : Data.ByteString.Lazy.ByteString
    -> Maybe { n : Data.Int.Int64 | 0 <= n && n < bllen bs }

assume findIndex
    :: (Data.Word.Word8 -> Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> Maybe { n : Data.Int.Int64 | 0 <= n && n < bllen bs }

assume findIndices
    :: (Data.Word.Word8 -> Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> [{ n : Data.Int.Int64 | 0 <= n && n < bllen bs }]

assume count
    :: Data.Word.Word8
    -> bs : Data.ByteString.Lazy.ByteString
    -> { n : Data.Int.Int64 | 0 <= n && n < bllen bs }

assume zip
    :: l : Data.ByteString.Lazy.ByteString
    -> r : Data.ByteString.Lazy.ByteString
    -> { o : [(Data.Word.Word8, Data.Word.Word8)] | len o <= bllen l && len o <= bllen r }

assume zipWith
    :: (Data.Word.Word8 -> Data.Word.Word8 -> a)
    -> l : Data.ByteString.Lazy.ByteString
    -> r : Data.ByteString.Lazy.ByteString
    -> { o : [a] | len o <= bllen l && len o <= bllen r }

assume unzip
    :: i : [(Data.Word.Word8, Data.Word.Word8)]
    -> ( { l : Data.ByteString.Lazy.ByteString | bllen l == len i }
       , { r : Data.ByteString.Lazy.ByteString | bllen r == len i }
       )

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
