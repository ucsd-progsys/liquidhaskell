module spec Data.ByteString.Lazy where

import Data.String
import Data.ByteString

measure bllen :: Data.ByteString.Lazy.ByteString -> { n : GHC.Int.Int64 | 0 <= n }

invariant { bs : Data.ByteString.Lazy.ByteString | 0 <= bllen bs }

invariant { bs : Data.ByteString.Lazy.ByteString | bllen bs == stringlen bs }

assume empty :: { bs : Data.ByteString.Lazy.ByteString | bllen bs == 0 }

assume singleton
    :: _ -> { bs : Data.ByteString.Lazy.ByteString | bllen bs == 1 }

assume pack
    :: w8s : [_]
    -> { bs : _ | bllen bs == len w8s }

assume unpack
    :: bs : Data.ByteString.Lazy.ByteString
    -> { w8s : [_] | len w8s == bllen bs }

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
    :: _
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i + 1 }

assume snoc
    :: i : Data.ByteString.Lazy.ByteString
    -> _
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i + 1 }

assume append
    :: l : Data.ByteString.Lazy.ByteString
    -> r : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen l + bllen r }

assume head
    :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> _

assume uncons
    :: i : Data.ByteString.Lazy.ByteString
    -> Maybe (_, { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i - 1 })

assume unsnoc
    :: i : Data.ByteString.Lazy.ByteString
    -> Maybe ({ o : Data.ByteString.Lazy.ByteString | bllen o == bllen i - 1 }, _)

assume last :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs } -> _

assume tail :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs } -> _

assume init :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs } -> _

assume null :: bs : Data.ByteString.Lazy.ByteString -> { b : GHC.Types.Bool | b <=> bllen bs == 0 }

assume length
    :: bs : Data.ByteString.Lazy.ByteString -> { n : GHC.Int.Int64 | bllen bs == n }

assume map
    :: (_ -> _)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume reverse
    :: i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume intersperse
    :: _
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | (bllen i == 0 <=> bllen o == 0) && (1 <= bllen i <=> bllen o == 2 * bllen i - 1) }

assume intercalate
    :: l : Data.ByteString.Lazy.ByteString
    -> rs : [Data.ByteString.Lazy.ByteString]
    -> { o : Data.ByteString.Lazy.ByteString | len rs == 0 ==> bllen o == 0 }

assume transpose
    :: is : [Data.ByteString.Lazy.ByteString]
    -> { os : [{ bs : Data.ByteString.Lazy.ByteString | bllen bs <= len is }] | len is == 0 ==> len os == 0}

assume foldl1
    :: (_ -> _ -> _)
    -> { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> _

assume foldl1'
    :: (_ -> _ -> _)
    -> { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> _

assume foldr1
    :: (_ -> _ -> _)
    -> { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> _

assume concat
    :: is : [Data.ByteString.Lazy.ByteString]
    -> { o : Data.ByteString.Lazy.ByteString | (len is == 0) ==> (bllen o == 0) }

assume concatMap
    :: (_ -> Data.ByteString.Lazy.ByteString)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen i == 0 ==> bllen o == 0 }

assume any :: (_ -> GHC.Types.Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> { b : GHC.Types.Bool | bllen bs == 0 ==> not b }

assume all :: (_ -> GHC.Types.Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> { b : GHC.Types.Bool | bllen bs == 0 ==> b }

assume maximum :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs } -> _

assume minimum :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs } -> _

assume scanl
    :: (_ -> _ -> _)
    -> _
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume mapAccumL
    :: (acc -> _ -> (acc, _))
    -> acc
    -> i : Data.ByteString.Lazy.ByteString
    -> (acc, { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i })

assume mapAccumR
    :: (acc -> _ -> (acc, _))
    -> acc
    -> i : Data.ByteString.Lazy.ByteString
    -> (acc, { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i })

assume replicate
    :: n : GHC.Int.Int64
    -> _
    -> { bs : Data.ByteString.Lazy.ByteString | bllen bs == n }

assume take
    :: n : GHC.Int.Int64
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | (n <= 0 ==> bllen o == 0) &&
                                               ((0 <= n && n <= bllen i) <=> bllen o == n) &&
                                               (bllen i <= n <=> bllen o = bllen i) }

assume drop
    :: n : GHC.Int.Int64
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | (n <= 0 <=> bllen o == bllen i) &&
                                               ((0 <= n && n <= bllen i) <=> bllen o == bllen i - n) &&
                                               (bllen i <= n <=> bllen o == 0) }

assume splitAt
    :: n : GHC.Int.Int64
    -> i : Data.ByteString.Lazy.ByteString
    -> ( { l : Data.ByteString.Lazy.ByteString | (n <= 0 <=> bllen l == 0) &&
                                                 ((0 <= n && n <= bllen i) <=> bllen l == n) &&
                                                 (bllen i <= n <=> bllen l == bllen i) }
       , { r : Data.ByteString.Lazy.ByteString | (n <= 0 <=> bllen r == bllen i) &&
                                                 ((0 <= n && n <= bllen i) <=> bllen r == bllen i - n) &&
                                                 (bllen i <= n <=> bllen r == 0) }
       )

assume takeWhile
    :: (_ -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }

assume dropWhile
    :: (_ -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }

assume span
    :: (_ -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> ( { l : Data.ByteString.Lazy.ByteString | bllen l <= bllen i }
       , { r : Data.ByteString.Lazy.ByteString | bllen r <= bllen i }
       )

assume break
    :: (_ -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> ( { l : Data.ByteString.Lazy.ByteString | bllen l <= bllen i }
       , { r : Data.ByteString.Lazy.ByteString | bllen r <= bllen i }
       )

assume group
    :: i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | 1 <= bllen o && bllen o <= bllen i }]

assume groupBy
    :: (_ -> _ -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | 1 <= bllen o && bllen o <= bllen i }]

assume inits
    :: i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }]

assume tails
    :: i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }]

assume split
    :: _
    -> i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }]

assume splitWith
    :: (_ -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }]

assume isPrefixOf
    :: l : Data.ByteString.Lazy.ByteString
    -> r : Data.ByteString.Lazy.ByteString
    -> { b : GHC.Types.Bool | bllen l >= bllen r ==> not b }

assume isSuffixOf
    :: l : Data.ByteString.Lazy.ByteString
    -> r : Data.ByteString.Lazy.ByteString
    -> { b : GHC.Types.Bool | bllen l >= bllen r ==> not b }

assume elem
    :: _
    -> bs : Data.ByteString.Lazy.ByteString
    -> { b : GHC.Types.Bool | (bllen bs == 0) ==> not b }

assume notElem
    :: _
    -> bs : Data.ByteString.Lazy.ByteString
    -> { b : GHC.Types.Bool | (bllen bs == 0) ==> b }

assume find
    :: (_ -> GHC.Types.Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> Maybe { w8 : _ | bllen bs /= 0 }

assume filter
    :: (_ -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }

assume partition
    :: (_ -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> ( { l : Data.ByteString.Lazy.ByteString | bllen l <= bllen i }
       , { r : Data.ByteString.Lazy.ByteString | bllen r <= bllen i }
       )

assume index
    :: bs : Data.ByteString.Lazy.ByteString
    -> { n : GHC.Int.Int64 | 0 <= n && n < bllen bs }
    -> _

assume elemIndex
    :: _
    -> bs : Data.ByteString.Lazy.ByteString
    -> Maybe { n : GHC.Int.Int64 | 0 <= n && n < bllen bs }

assume elemIndices
    :: _
    -> bs : Data.ByteString.Lazy.ByteString
    -> [{ n : GHC.Int.Int64 | 0 <= n && n < bllen bs }]

assume elemIndexEnd
    :: _
    -> bs : Data.ByteString.Lazy.ByteString
    -> Maybe { n : GHC.Int.Int64 | 0 <= n && n < bllen bs }

assume findIndex
    :: (_ -> GHC.Types.Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> Maybe { n : GHC.Int.Int64 | 0 <= n && n < bllen bs }

assume findIndices
    :: (_ -> GHC.Types.Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> [{ n : GHC.Int.Int64 | 0 <= n && n < bllen bs }]

assume count
    :: _
    -> bs : Data.ByteString.Lazy.ByteString
    -> { n : GHC.Int.Int64 | 0 <= n && n < bllen bs }

assume zip
    :: l : Data.ByteString.Lazy.ByteString
    -> r : Data.ByteString.Lazy.ByteString
    -> { o : [(_, _)] | len o <= bllen l && len o <= bllen r }

assume zipWith
    :: (_ -> _ -> a)
    -> l : Data.ByteString.Lazy.ByteString
    -> r : Data.ByteString.Lazy.ByteString
    -> { o : [a] | len o <= bllen l && len o <= bllen r }

assume unzip
    :: i : [(_, _)]
    -> ( { l : Data.ByteString.Lazy.ByteString | bllen l == len i }
       , { r : Data.ByteString.Lazy.ByteString | bllen r == len i }
       )

assume copy
    :: i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume hGet
    :: _
    -> n : { n : Int | 0 <= n }
    -> IO { bs : Data.ByteString.Lazy.ByteString | bllen bs == n || bllen bs == 0 }

assume hGetNonBlocking
    :: _
    -> n : { n : Int | 0 <= n }
    -> IO { bs : Data.ByteString.Lazy.ByteString | bllen bs <= n }
