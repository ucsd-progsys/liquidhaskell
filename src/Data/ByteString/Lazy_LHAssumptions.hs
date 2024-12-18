{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Data.ByteString.Lazy_LHAssumptions where

import qualified Data.ByteString
import Data.ByteString_LHAssumptions()
import Data.ByteString.Lazy
import Data.Int
import Data.String_LHAssumptions()
import GHC.Int_LHAssumptions()

{-@
measure bllen :: ByteString -> { n : Int64 | 0 <= n }

invariant { bs : ByteString | 0 <= bllen bs }

invariant { bs : ByteString | bllen bs == stringlen bs }

assume empty :: { bs : ByteString | bllen bs == 0 }

assume singleton
    :: _ -> { bs : ByteString | bllen bs == 1 }

assume pack
    :: w8s : [_]
    -> { bs : _ | bllen bs == len w8s }

assume unpack
    :: bs : ByteString
    -> { w8s : [_] | len w8s == bllen bs }

assume fromStrict
    :: i : Data.ByteString.ByteString
    -> { o : ByteString | bllen o == bslen i }

assume toStrict
    :: i : ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bllen i }

assume fromChunks
    :: i : [Data.ByteString.ByteString]
    -> { o : ByteString | len i == 0 <=> bllen o == 0 }

assume toChunks
    :: i : ByteString
    -> { os : [{ o : Data.ByteString.ByteString | bslen o <= bllen i}] | len os == 0 <=> bllen i == 0 }

assume Data.ByteString.Lazy.cons
    :: _
    -> i : ByteString
    -> { o : ByteString | bllen o == bllen i + 1 }

assume Data.ByteString.Lazy.snoc
    :: i : ByteString
    -> _
    -> { o : ByteString | bllen o == bllen i + 1 }

assume Data.ByteString.Lazy.append
    :: l : ByteString
    -> r : ByteString
    -> { o : ByteString | bllen o == bllen l + bllen r }

assume Data.ByteString.Lazy.head
    :: { bs : ByteString | 1 <= bllen bs }
    -> _

assume Data.ByteString.Lazy.uncons
    :: i : ByteString
    -> Maybe (_, { o : ByteString | bllen o == bllen i - 1 })

assume Data.ByteString.Lazy.unsnoc
    :: i : ByteString
    -> Maybe ({ o : ByteString | bllen o == bllen i - 1 }, _)

assume Data.ByteString.Lazy.last :: { bs : ByteString | 1 <= bllen bs } -> _

assume Data.ByteString.Lazy.tail :: { bs : ByteString | 1 <= bllen bs } -> _

assume Data.ByteString.Lazy.init :: { bs : ByteString | 1 <= bllen bs } -> _

assume Data.ByteString.Lazy.null :: bs : ByteString -> { b : Bool | b <=> bllen bs == 0 }

assume Data.ByteString.Lazy.length
    :: bs : ByteString -> { n : Int64 | bllen bs == n }

assume Data.ByteString.Lazy.map
    :: (_ -> _)
    -> i : ByteString
    -> { o : ByteString | bllen o == bllen i }

assume Data.ByteString.Lazy.reverse
    :: i : ByteString
    -> { o : ByteString | bllen o == bllen i }

assume Data.ByteString.Lazy.intersperse
    :: _
    -> i : ByteString
    -> { o : ByteString | (bllen i == 0 <=> bllen o == 0) && (1 <= bllen i <=> bllen o == 2 * bllen i - 1) }

assume Data.ByteString.Lazy.intercalate
    :: l : ByteString
    -> rs : [ByteString]
    -> { o : ByteString | len rs == 0 ==> bllen o == 0 }

assume Data.ByteString.Lazy.transpose
    :: is : [ByteString]
    -> { os : [{ bs : ByteString | bllen bs <= len is }] | len is == 0 ==> len os == 0}

assume Data.ByteString.Lazy.foldl1
    :: (_ -> _ -> _)
    -> { bs : ByteString | 1 <= bllen bs }
    -> _

assume Data.ByteString.Lazy.foldl1'
    :: (_ -> _ -> _)
    -> { bs : ByteString | 1 <= bllen bs }
    -> _

assume Data.ByteString.Lazy.foldr1
    :: (_ -> _ -> _)
    -> { bs : ByteString | 1 <= bllen bs }
    -> _

assume Data.ByteString.Lazy.concat
    :: is : [ByteString]
    -> { o : ByteString | (len is == 0) ==> (bllen o == 0) }

assume Data.ByteString.Lazy.concatMap
    :: (_ -> ByteString)
    -> i : ByteString
    -> { o : ByteString | bllen i == 0 ==> bllen o == 0 }

assume Data.ByteString.Lazy.any :: (_ -> Bool)
    -> bs : ByteString
    -> { b : Bool | bllen bs == 0 ==> not b }

assume Data.ByteString.Lazy.all :: (_ -> Bool)
    -> bs : ByteString
    -> { b : Bool | bllen bs == 0 ==> b }

assume Data.ByteString.Lazy.maximum :: { bs : ByteString | 1 <= bllen bs } -> _

assume Data.ByteString.Lazy.minimum :: { bs : ByteString | 1 <= bllen bs } -> _

assume Data.ByteString.Lazy.scanl
    :: (_ -> _ -> _)
    -> _
    -> i : ByteString
    -> { o : ByteString | bllen o == bllen i }

assume Data.ByteString.Lazy.mapAccumL
    :: (acc -> _ -> (acc, _))
    -> acc
    -> i : ByteString
    -> (acc, { o : ByteString | bllen o == bllen i })

assume Data.ByteString.Lazy.mapAccumR
    :: (acc -> _ -> (acc, _))
    -> acc
    -> i : ByteString
    -> (acc, { o : ByteString | bllen o == bllen i })

assume Data.ByteString.Lazy.replicate
    :: n : Int64
    -> _
    -> { bs : ByteString | bllen bs == n }

assume Data.ByteString.Lazy.take
    :: n : Int64
    -> i : ByteString
    -> { o : ByteString | (n <= 0 ==> bllen o == 0) &&
                                               ((0 <= n && n <= bllen i) <=> bllen o == n) &&
                                               (bllen i <= n <=> bllen o = bllen i) }

assume Data.ByteString.Lazy.drop
    :: n : Int64
    -> i : ByteString
    -> { o : ByteString | (n <= 0 <=> bllen o == bllen i) &&
                                               ((0 <= n && n <= bllen i) <=> bllen o == bllen i - n) &&
                                               (bllen i <= n <=> bllen o == 0) }

assume Data.ByteString.Lazy.splitAt
    :: n : Int64
    -> i : ByteString
    -> ( { l : ByteString | (n <= 0 <=> bllen l == 0) &&
                                                 ((0 <= n && n <= bllen i) <=> bllen l == n) &&
                                                 (bllen i <= n <=> bllen l == bllen i) }
       , { r : ByteString | (n <= 0 <=> bllen r == bllen i) &&
                                                 ((0 <= n && n <= bllen i) <=> bllen r == bllen i - n) &&
                                                 (bllen i <= n <=> bllen r == 0) }
       )

assume Data.ByteString.Lazy.takeWhile
    :: (_ -> Bool)
    -> i : ByteString
    -> { o : ByteString | bllen o <= bllen i }

assume Data.ByteString.Lazy.dropWhile
    :: (_ -> Bool)
    -> i : ByteString
    -> { o : ByteString | bllen o <= bllen i }

assume Data.ByteString.Lazy.span
    :: (_ -> Bool)
    -> i : ByteString
    -> ( { l : ByteString | bllen l <= bllen i }
       , { r : ByteString | bllen r <= bllen i }
       )

assume Data.ByteString.Lazy.break
    :: (_ -> Bool)
    -> i : ByteString
    -> ( { l : ByteString | bllen l <= bllen i }
       , { r : ByteString | bllen r <= bllen i }
       )

assume Data.ByteString.Lazy.group
    :: i : ByteString
    -> [{ o : ByteString | 1 <= bllen o && bllen o <= bllen i }]

assume Data.ByteString.Lazy.groupBy
    :: (_ -> _ -> Bool)
    -> i : ByteString
    -> [{ o : ByteString | 1 <= bllen o && bllen o <= bllen i }]

assume Data.ByteString.Lazy.inits
    :: i : ByteString
    -> [{ o : ByteString | bllen o <= bllen i }]

assume Data.ByteString.Lazy.tails
    :: i : ByteString
    -> [{ o : ByteString | bllen o <= bllen i }]

assume Data.ByteString.Lazy.split
    :: _
    -> i : ByteString
    -> [{ o : ByteString | bllen o <= bllen i }]

assume Data.ByteString.Lazy.splitWith
    :: (_ -> Bool)
    -> i : ByteString
    -> [{ o : ByteString | bllen o <= bllen i }]

assume Data.ByteString.Lazy.isPrefixOf
    :: l : ByteString
    -> r : ByteString
    -> { b : Bool | bllen l >= bllen r ==> not b }

assume Data.ByteString.Lazy.isSuffixOf
    :: l : ByteString
    -> r : ByteString
    -> { b : Bool | bllen l >= bllen r ==> not b }

assume Data.ByteString.Lazy.elem
    :: _
    -> bs : ByteString
    -> { b : Bool | (bllen bs == 0) ==> not b }

assume Data.ByteString.Lazy.notElem
    :: _
    -> bs : ByteString
    -> { b : Bool | (bllen bs == 0) ==> b }

assume Data.ByteString.Lazy.find
    :: (_ -> Bool)
    -> bs : ByteString
    -> Maybe { w8 : _ | bllen bs /= 0 }

assume Data.ByteString.Lazy.filter
    :: (_ -> Bool)
    -> i : ByteString
    -> { o : ByteString | bllen o <= bllen i }

assume Data.ByteString.Lazy.partition
    :: (_ -> Bool)
    -> i : ByteString
    -> ( { l : ByteString | bllen l <= bllen i }
       , { r : ByteString | bllen r <= bllen i }
       )

assume Data.ByteString.Lazy.index
    :: bs : ByteString
    -> { n : Int64 | 0 <= n && n < bllen bs }
    -> _

assume Data.ByteString.Lazy.elemIndex
    :: _
    -> bs : ByteString
    -> Maybe { n : Int64 | 0 <= n && n < bllen bs }

assume Data.ByteString.Lazy.elemIndices
    :: _
    -> bs : ByteString
    -> [{ n : Int64 | 0 <= n && n < bllen bs }]

assume Data.ByteString.Lazy.elemIndexEnd
    :: _
    -> bs : ByteString
    -> Maybe { n : Int64 | 0 <= n && n < bllen bs }

assume Data.ByteString.Lazy.findIndex
    :: (_ -> Bool)
    -> bs : ByteString
    -> Maybe { n : Int64 | 0 <= n && n < bllen bs }

assume Data.ByteString.Lazy.findIndices
    :: (_ -> Bool)
    -> bs : ByteString
    -> [{ n : Int64 | 0 <= n && n < bllen bs }]

assume Data.ByteString.Lazy.count
    :: _
    -> bs : ByteString
    -> { n : Int64 | 0 <= n && n < bllen bs }

assume Data.ByteString.Lazy.zip
    :: l : ByteString
    -> r : ByteString
    -> { o : [(_, _)] | len o <= bllen l && len o <= bllen r }

assume Data.ByteString.Lazy.zipWith
    :: (_ -> _ -> a)
    -> l : ByteString
    -> r : ByteString
    -> { o : [a] | len o <= bllen l && len o <= bllen r }

assume Data.ByteString.Lazy.unzip
    :: i : [(_, _)]
    -> ( { l : ByteString | bllen l == len i }
       , { r : ByteString | bllen r == len i }
       )

assume Data.ByteString.Lazy.copy
    :: i : ByteString
    -> { o : ByteString | bllen o == bllen i }

assume Data.ByteString.Lazy.hGet
    :: _
    -> n : { n : Int | 0 <= n }
    -> IO { bs : ByteString | bllen bs == n || bllen bs == 0 }

assume Data.ByteString.Lazy.hGetNonBlocking
    :: _
    -> n : { n : Int | 0 <= n }
    -> IO { bs : ByteString | bllen bs <= n }
@-}
