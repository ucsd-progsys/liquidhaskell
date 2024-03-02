{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Data.ByteString.Lazy_LHAssumptions where

import Data.ByteString
import Data.ByteString_LHAssumptions()
import Data.ByteString.Lazy
import Data.String_LHAssumptions()
import GHC.Int_LHAssumptions()

{-@
measure bllen :: Data.ByteString.Lazy.ByteString -> { n : GHC.Internal.Int.Int64 | 0 <= n }

invariant { bs : Data.ByteString.Lazy.ByteString | 0 <= bllen bs }

invariant { bs : Data.ByteString.Lazy.ByteString | bllen bs == stringlen bs }

assume Data.ByteString.Lazy.empty :: { bs : Data.ByteString.Lazy.ByteString | bllen bs == 0 }

assume Data.ByteString.Lazy.singleton
    :: _ -> { bs : Data.ByteString.Lazy.ByteString | bllen bs == 1 }

assume Data.ByteString.Lazy.pack
    :: w8s : [_]
    -> { bs : _ | bllen bs == len w8s }

assume Data.ByteString.Lazy.unpack
    :: bs : Data.ByteString.Lazy.ByteString
    -> { w8s : [_] | len w8s == bllen bs }

assume Data.ByteString.Lazy.Internal.fromStrict
    :: i : Data.ByteString.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bslen i }

assume Data.ByteString.Lazy.Internal.toStrict
    :: i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bllen i }

assume Data.ByteString.Lazy.fromChunks
    :: i : [Data.ByteString.ByteString]
    -> { o : Data.ByteString.Lazy.ByteString | len i == 0 <=> bllen o == 0 }

assume Data.ByteString.Lazy.toChunks
    :: i : Data.ByteString.Lazy.ByteString
    -> { os : [{ o : Data.ByteString.ByteString | bslen o <= bllen i}] | len os == 0 <=> bllen i == 0 }

assume Data.ByteString.Lazy.cons
    :: _
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i + 1 }

assume Data.ByteString.Lazy.snoc
    :: i : Data.ByteString.Lazy.ByteString
    -> _
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i + 1 }

assume Data.ByteString.Lazy.append
    :: l : Data.ByteString.Lazy.ByteString
    -> r : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen l + bllen r }

assume Data.ByteString.Lazy.head
    :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> _

assume Data.ByteString.Lazy.uncons
    :: i : Data.ByteString.Lazy.ByteString
    -> Maybe (_, { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i - 1 })

assume Data.ByteString.Lazy.unsnoc
    :: i : Data.ByteString.Lazy.ByteString
    -> Maybe ({ o : Data.ByteString.Lazy.ByteString | bllen o == bllen i - 1 }, _)

assume Data.ByteString.Lazy.last :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs } -> _

assume Data.ByteString.Lazy.tail :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs } -> _

assume Data.ByteString.Lazy.init :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs } -> _

assume Data.ByteString.Lazy.null :: bs : Data.ByteString.Lazy.ByteString -> { b : GHC.Types.Bool | b <=> bllen bs == 0 }

assume Data.ByteString.Lazy.length
    :: bs : Data.ByteString.Lazy.ByteString -> { n : GHC.Internal.Int.Int64 | bllen bs == n }

assume Data.ByteString.Lazy.map
    :: (_ -> _)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume Data.ByteString.Lazy.reverse
    :: i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume Data.ByteString.Lazy.intersperse
    :: _
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | (bllen i == 0 <=> bllen o == 0) && (1 <= bllen i <=> bllen o == 2 * bllen i - 1) }

assume Data.ByteString.Lazy.intercalate
    :: l : Data.ByteString.Lazy.ByteString
    -> rs : [Data.ByteString.Lazy.ByteString]
    -> { o : Data.ByteString.Lazy.ByteString | len rs == 0 ==> bllen o == 0 }

assume Data.ByteString.Lazy.transpose
    :: is : [Data.ByteString.Lazy.ByteString]
    -> { os : [{ bs : Data.ByteString.Lazy.ByteString | bllen bs <= len is }] | len is == 0 ==> len os == 0}

assume Data.ByteString.Lazy.foldl1
    :: (_ -> _ -> _)
    -> { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> _

assume Data.ByteString.Lazy.foldl1'
    :: (_ -> _ -> _)
    -> { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> _

assume Data.ByteString.Lazy.foldr1
    :: (_ -> _ -> _)
    -> { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> _

assume Data.ByteString.Lazy.concat
    :: is : [Data.ByteString.Lazy.ByteString]
    -> { o : Data.ByteString.Lazy.ByteString | (len is == 0) ==> (bllen o == 0) }

assume Data.ByteString.Lazy.concatMap
    :: (_ -> Data.ByteString.Lazy.ByteString)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen i == 0 ==> bllen o == 0 }

assume Data.ByteString.Lazy.any :: (_ -> GHC.Types.Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> { b : GHC.Types.Bool | bllen bs == 0 ==> not b }

assume Data.ByteString.Lazy.all :: (_ -> GHC.Types.Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> { b : GHC.Types.Bool | bllen bs == 0 ==> b }

assume Data.ByteString.Lazy.maximum :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs } -> _

assume Data.ByteString.Lazy.minimum :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs } -> _

assume Data.ByteString.Lazy.scanl
    :: (_ -> _ -> _)
    -> _
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume Data.ByteString.Lazy.mapAccumL
    :: (acc -> _ -> (acc, _))
    -> acc
    -> i : Data.ByteString.Lazy.ByteString
    -> (acc, { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i })

assume Data.ByteString.Lazy.mapAccumR
    :: (acc -> _ -> (acc, _))
    -> acc
    -> i : Data.ByteString.Lazy.ByteString
    -> (acc, { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i })

assume Data.ByteString.Lazy.replicate
    :: n : GHC.Internal.Int.Int64
    -> _
    -> { bs : Data.ByteString.Lazy.ByteString | bllen bs == n }

assume Data.ByteString.Lazy.take
    :: n : GHC.Internal.Int.Int64
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | (n <= 0 ==> bllen o == 0) &&
                                               ((0 <= n && n <= bllen i) <=> bllen o == n) &&
                                               (bllen i <= n <=> bllen o = bllen i) }

assume Data.ByteString.Lazy.drop
    :: n : GHC.Internal.Int.Int64
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | (n <= 0 <=> bllen o == bllen i) &&
                                               ((0 <= n && n <= bllen i) <=> bllen o == bllen i - n) &&
                                               (bllen i <= n <=> bllen o == 0) }

assume Data.ByteString.Lazy.splitAt
    :: n : GHC.Internal.Int.Int64
    -> i : Data.ByteString.Lazy.ByteString
    -> ( { l : Data.ByteString.Lazy.ByteString | (n <= 0 <=> bllen l == 0) &&
                                                 ((0 <= n && n <= bllen i) <=> bllen l == n) &&
                                                 (bllen i <= n <=> bllen l == bllen i) }
       , { r : Data.ByteString.Lazy.ByteString | (n <= 0 <=> bllen r == bllen i) &&
                                                 ((0 <= n && n <= bllen i) <=> bllen r == bllen i - n) &&
                                                 (bllen i <= n <=> bllen r == 0) }
       )

assume Data.ByteString.Lazy.takeWhile
    :: (_ -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }

assume Data.ByteString.Lazy.dropWhile
    :: (_ -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }

assume Data.ByteString.Lazy.span
    :: (_ -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> ( { l : Data.ByteString.Lazy.ByteString | bllen l <= bllen i }
       , { r : Data.ByteString.Lazy.ByteString | bllen r <= bllen i }
       )

assume Data.ByteString.Lazy.break
    :: (_ -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> ( { l : Data.ByteString.Lazy.ByteString | bllen l <= bllen i }
       , { r : Data.ByteString.Lazy.ByteString | bllen r <= bllen i }
       )

assume Data.ByteString.Lazy.group
    :: i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | 1 <= bllen o && bllen o <= bllen i }]

assume Data.ByteString.Lazy.groupBy
    :: (_ -> _ -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | 1 <= bllen o && bllen o <= bllen i }]

assume Data.ByteString.Lazy.inits
    :: i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }]

assume Data.ByteString.Lazy.tails
    :: i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }]

assume Data.ByteString.Lazy.split
    :: _
    -> i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }]

assume Data.ByteString.Lazy.splitWith
    :: (_ -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }]

assume Data.ByteString.Lazy.isPrefixOf
    :: l : Data.ByteString.Lazy.ByteString
    -> r : Data.ByteString.Lazy.ByteString
    -> { b : GHC.Types.Bool | bllen l >= bllen r ==> not b }

assume Data.ByteString.Lazy.isSuffixOf
    :: l : Data.ByteString.Lazy.ByteString
    -> r : Data.ByteString.Lazy.ByteString
    -> { b : GHC.Types.Bool | bllen l >= bllen r ==> not b }

assume Data.ByteString.Lazy.elem
    :: _
    -> bs : Data.ByteString.Lazy.ByteString
    -> { b : GHC.Types.Bool | (bllen bs == 0) ==> not b }

assume Data.ByteString.Lazy.notElem
    :: _
    -> bs : Data.ByteString.Lazy.ByteString
    -> { b : GHC.Types.Bool | (bllen bs == 0) ==> b }

assume Data.ByteString.Lazy.find
    :: (_ -> GHC.Types.Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> Maybe { w8 : _ | bllen bs /= 0 }

assume Data.ByteString.Lazy.filter
    :: (_ -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }

assume Data.ByteString.Lazy.partition
    :: (_ -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> ( { l : Data.ByteString.Lazy.ByteString | bllen l <= bllen i }
       , { r : Data.ByteString.Lazy.ByteString | bllen r <= bllen i }
       )

assume Data.ByteString.Lazy.index
    :: bs : Data.ByteString.Lazy.ByteString
    -> { n : GHC.Internal.Int.Int64 | 0 <= n && n < bllen bs }
    -> _

assume Data.ByteString.Lazy.elemIndex
    :: _
    -> bs : Data.ByteString.Lazy.ByteString
    -> Maybe { n : GHC.Internal.Int.Int64 | 0 <= n && n < bllen bs }

assume Data.ByteString.Lazy.elemIndices
    :: _
    -> bs : Data.ByteString.Lazy.ByteString
    -> [{ n : GHC.Internal.Int.Int64 | 0 <= n && n < bllen bs }]

assume Data.ByteString.Lazy.elemIndexEnd
    :: _
    -> bs : Data.ByteString.Lazy.ByteString
    -> Maybe { n : GHC.Internal.Int.Int64 | 0 <= n && n < bllen bs }

assume Data.ByteString.Lazy.findIndex
    :: (_ -> GHC.Types.Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> Maybe { n : GHC.Internal.Int.Int64 | 0 <= n && n < bllen bs }

assume Data.ByteString.Lazy.findIndices
    :: (_ -> GHC.Types.Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> [{ n : GHC.Internal.Int.Int64 | 0 <= n && n < bllen bs }]

assume Data.ByteString.Lazy.count
    :: _
    -> bs : Data.ByteString.Lazy.ByteString
    -> { n : GHC.Internal.Int.Int64 | 0 <= n && n < bllen bs }

assume Data.ByteString.Lazy.zip
    :: l : Data.ByteString.Lazy.ByteString
    -> r : Data.ByteString.Lazy.ByteString
    -> { o : [(_, _)] | len o <= bllen l && len o <= bllen r }

assume Data.ByteString.Lazy.zipWith
    :: (_ -> _ -> a)
    -> l : Data.ByteString.Lazy.ByteString
    -> r : Data.ByteString.Lazy.ByteString
    -> { o : [a] | len o <= bllen l && len o <= bllen r }

assume Data.ByteString.Lazy.unzip
    :: i : [(_, _)]
    -> ( { l : Data.ByteString.Lazy.ByteString | bllen l == len i }
       , { r : Data.ByteString.Lazy.ByteString | bllen r == len i }
       )

assume Data.ByteString.Lazy.copy
    :: i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume Data.ByteString.Lazy.hGet
    :: _
    -> n : { n : Int | 0 <= n }
    -> IO { bs : Data.ByteString.Lazy.ByteString | bllen bs == n || bllen bs == 0 }

assume Data.ByteString.Lazy.hGetNonBlocking
    :: _
    -> n : { n : Int | 0 <= n }
    -> IO { bs : Data.ByteString.Lazy.ByteString | bllen bs <= n }
@-}
