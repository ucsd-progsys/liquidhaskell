module spec Data.ByteString.Char8 where

import Data.ByteString 

assume empty :: { bs : Data.ByteString.ByteString | bslen bs == 0 }

assume singleton
    :: Char -> { bs : Data.ByteString.ByteString | bslen bs == 1 }

assume pack
    :: w8s : [Char]
    -> { bs : Data.ByteString.ByteString | bslen bs == len w8s }

assume unpack
    :: bs : Data.ByteString.ByteString
    -> { w8s : [Char] | len w8s == bslen bs }

assume cons
    :: Char
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i + 1 }

assume snoc
    :: i : Data.ByteString.ByteString
    -> Char
    -> { o : Data.ByteString.ByteString | bslen o == bslen i + 1 }

assume append
    :: l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen l + bslen r }

head :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> Char

assume uncons
    :: i : Data.ByteString.ByteString
    -> Maybe (Char, { o : Data.ByteString.ByteString | bslen o == bslen i - 1 })

assume unsnoc
    :: i : Data.ByteString.ByteString
    -> Maybe ({ o : Data.ByteString.ByteString | bslen o == bslen i - 1 }, Char)

assume last :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> Char

assume tail :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> Char

assume init :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> Char

assume null
    :: bs : Data.ByteString.ByteString
    -> { b : Bool | b <=> bslen bs == 0 }

assume length :: bs : Data.ByteString.ByteString -> { n : Int | bslen bs == n }

assume map
    :: (Char -> Char)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume reverse
    :: i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume intersperse
    :: Char
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
    :: (Char -> Char -> Char)
    -> { bs : Data.ByteString.ByteString | 1 <= bslen bs }
    -> Char

foldl1'
    :: (Char -> Char -> Char)
    -> { bs : Data.ByteString.ByteString | 1 <= bslen bs }
    -> Char

foldr1
    :: (Char -> Char -> Char)
    -> { bs : Data.ByteString.ByteString | 1 <= bslen bs }
    -> Char

foldr1'
    :: (Char -> Char -> Char)
    -> { bs : Data.ByteString.ByteString | 1 <= bslen bs }
    -> Char

assume concat
    :: is : [Data.ByteString.ByteString]
    -> { o : Data.ByteString.ByteString | len is == 0 ==> bslen o }

assume concatMap
    :: (Char -> Data.ByteString.ByteString)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen i == 0 ==> bslen o == 0 }

assume any :: (Char -> Bool)
    -> bs : Data.ByteString.ByteString
    -> { b : Bool | bslen bs == 0 ==> not b }

assume all :: (Char -> Bool)
    -> bs : Data.ByteString.ByteString
    -> { b : Bool | bslen bs == 0 ==> b }

maximum
    :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> Char

minimum
    :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> Char

assume scanl
    :: (Char -> Char -> Char)
    -> Char
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume scanl1
    :: (Char -> Char -> Char)
    -> i : { i : Data.ByteString.ByteString | 1 <= bslen i }
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume scanr
    :: (Char -> Char -> Char)
    -> Char
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume scanr1
    :: (Char -> Char -> Char)
    -> i : { i : Data.ByteString.ByteString | 1 <= bslen i }
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume mapAccumL
    :: (acc -> Char -> (acc, Char))
    -> acc
    -> i : Data.ByteString.ByteString
    -> (acc, { o : Data.ByteString.ByteString | bslen o == bslen i })

assume mapAccumR
    :: (acc -> Char -> (acc, Char))
    -> acc
    -> i : Data.ByteString.ByteString
    -> (acc, { o : Data.ByteString.ByteString | bslen o == bslen i })

assume replicate
    :: n : Int
    -> Char
    -> { bs : Data.ByteString.ByteString | bslen bs == n }

assume unfoldrN
    :: n : Int
    -> (a -> Maybe (Char, a))
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
    :: (Char -> Bool)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o <= bslen i }

assume dropWhile
    :: (Char -> Bool)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o <= bslen i }

assume span
    :: (Char -> Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

assume spanEnd
    :: (Char -> Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

assume break
    :: (Char -> Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

assume breakEnd
    :: (Char -> Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

assume group
    :: i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | 1 <= bslen o && bslen o <= bslen i }]

assume groupBy
    :: (Char -> Char -> Bool)
    -> i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | 1 <= bslen o && bslen o <= bslen i }]

assume inits
    :: i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | bslen o <= bslen i }]

assume tails
    :: i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | bslen o <= bslen i }]

assume split
    :: Char
    -> i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | bslen o <= bslen i }]

assume splitWith
    :: (Char -> Bool)
    -> i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | bslen o <= bslen i }]

assume lines
    :: i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | bslen o <= bslen i }]

assume words
    :: i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | bslen o <= bslen i }]

assume unlines
    :: is : [Data.ByteString.ByteString]
    -> { o : Data.ByteString.ByteString | (len is == 0 <=> bslen o == 0) && bslen o >= len is }

assume unwords
    :: is : [Data.ByteString.ByteString]
    -> { o : Data.ByteString.ByteString | (len is == 0 ==> bslen o == 0) && (1 <= len is ==> bslen o >= len is - 1) }

assume isPrefixOf
    :: l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { b : Bool | bslen l >= bslen r ==> not b }

assume isSuffixOf
    :: l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { b : Bool | bslen l > bslen r ==> not b }

assume isInfixOf
    :: l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { b : Bool | bslen l > bslen r ==> not b }

assume breakSubstring
    :: il : Data.ByteString.ByteString
    -> ir : Data.ByteString.ByteString
    -> ( { ol : Data.ByteString.ByteString | bslen ol <= bslen ir && (bslen il > bslen ir ==> bslen ol == bslen ir)}
       , { or : Data.ByteString.ByteString | bslen or <= bslen ir && (bslen il > bslen ir ==> bslen or == 0) }
       )

assume elem
    :: Char
    -> bs : Data.ByteString.ByteString
    -> { b : Bool | bslen b == 0 ==> not b }

assume notElem
    :: Char
    -> bs : Data.ByteString.ByteString
    -> { b : Bool | bslen b == 0 ==> b }

assume find
    :: (Char -> Bool)
    -> bs : Data.ByteString.ByteString
    -> Maybe { w8 : Char | bslen bs /= 0 }

assume filter
    :: (Char -> Bool)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o <= bslen i }

index
    :: bs : Data.ByteString.ByteString
    -> { n : Int | 0 <= n && n < bslen bs }
    -> Char

assume elemIndex
    :: Char
    -> bs : Data.ByteString.ByteString
    -> Maybe { n : Int | 0 <= n && n < bslen bs }

assume elemIndices
    :: Char
    -> bs : Data.ByteString.ByteString
    -> [{ n : Int | 0 <= n && n < bslen bs }]

assume elemIndexEnd
    :: Char
    -> bs : Data.ByteString.ByteString
    -> Maybe { n : Int | 0 <= n && n < bslen bs }

assume findIndex
    :: (Char -> Bool)
    -> bs : Data.ByteString.ByteString
    -> Maybe { n : Int | 0 <= n && n < bslen bs }

assume findIndices
    :: (Char -> Bool)
    -> bs : Data.ByteString.ByteString
    -> [{ n : Int | 0 <= n && n < bslen bs }]

assume count
    :: Char
    -> bs : Data.ByteString.ByteString
    -> { n : Int | 0 <= n && n < bslen bs }

assume zip
    :: l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { o : [(Char, Char)] | len o <= bslen l && len o <= bslen r }

assume zipWith
    :: (Char -> Char -> a)
    -> l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { o : [a] | len o <= bslen l && len o <= bslen r }

assume unzip
    :: i : [(Char, Char)]
    -> ( { l : Data.ByteString.ByteString | bslen l == len i }
       , { r : Data.ByteString.ByteString | bslen r == len i }
       )

assume sort
    :: i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume readInt
    :: i : Data.ByteString.ByteString
    -> Maybe { p : (Int, { o : Data.ByteString.ByteString | bslen o < bslen i}) | bslen i /= 0 }

assume readInteger
    :: i : Data.ByteString.ByteString
    -> Maybe { p : (Integer, { o : Data.ByteString.ByteString | bslen o < bslen i}) | bslen i /= 0 }

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

// assume partition
    // :: (Char -> Bool)
    // -> i : Data.ByteString.ByteString
    // -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       // , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       // )
