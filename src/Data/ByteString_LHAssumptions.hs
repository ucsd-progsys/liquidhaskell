{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Data.ByteString_LHAssumptions where

import Data.ByteString
import Data.String_LHAssumptions()
import GHC.Word

{-@
measure bslen :: Data.ByteString.ByteString -> { n : Int | 0 <= n }

invariant { bs : Data.ByteString.ByteString  | 0 <= bslen bs }

invariant { bs : Data.ByteString.ByteString | bslen bs == stringlen bs }

assume Data.ByteString.Internal.Type.empty :: { bs : Data.ByteString.ByteString | bslen bs == 0 }

assume Data.ByteString.singleton :: _ -> { bs : Data.ByteString.ByteString | bslen bs == 1 }

assume Data.ByteString.pack :: w8s : [_]
     -> { bs : Data.ByteString.ByteString | bslen bs == len w8s }

assume Data.ByteString.unpack :: bs : Data.ByteString.ByteString
       -> { w8s : [_] | len w8s == bslen bs }

assume Data.ByteString.cons :: _
     -> i : Data.ByteString.ByteString
     -> { o : Data.ByteString.ByteString | bslen o == bslen i + 1 }

assume Data.ByteString.snoc :: i : Data.ByteString.ByteString
     -> _
     -> { o : Data.ByteString.ByteString | bslen o == bslen i + 1 }

assume Data.ByteString.append :: l : Data.ByteString.ByteString
       -> r : Data.ByteString.ByteString
       -> { o : Data.ByteString.ByteString | bslen o == bslen l + bslen r }

assume Data.ByteString.head :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> _

assume Data.ByteString.unsnoc :: i:Data.ByteString.ByteString
       -> (Maybe ({ o : Data.ByteString.ByteString | bslen o == bslen i - 1 }, _))

assume Data.ByteString.last :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> _

assume Data.ByteString.tail :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> _

assume Data.ByteString.init
  :: {i:Data.ByteString.ByteString | 1 <= bslen i }
  -> {o:Data.ByteString.ByteString | bslen o == bslen i - 1 }

assume Data.ByteString.null
  :: bs : Data.ByteString.ByteString
  -> { b : GHC.Types.Bool | b <=> bslen bs == 0 }

assume Data.ByteString.length :: bs : Data.ByteString.ByteString -> { n : Int | bslen bs == n }

assume Data.ByteString.map
  :: (_ -> _)
  -> i : Data.ByteString.ByteString
  -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume Data.ByteString.reverse
  :: i : Data.ByteString.ByteString
  -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume Data.ByteString.intersperse
  :: _
  -> i : Data.ByteString.ByteString
  -> { o : Data.ByteString.ByteString | (bslen i == 0 <=> bslen o == 0) && (1 <= bslen i <=> bslen o == 2 * bslen i - 1) }

assume Data.ByteString.intercalate
  :: l : Data.ByteString.ByteString
  -> rs : [Data.ByteString.ByteString]
  -> { o : Data.ByteString.ByteString | len rs == 0 ==> bslen o == 0 }

assume Data.ByteString.transpose
  :: is : [Data.ByteString.ByteString]
  -> { os : [{ bs : Data.ByteString.ByteString | bslen bs <= len is }] | len is == 0 ==> len os == 0}

assume Data.ByteString.foldl1
  :: (_ -> _ -> _)
  -> { bs : Data.ByteString.ByteString | 1 <= bslen bs }
  -> _

assume Data.ByteString.foldl1'
  :: (_ -> _ -> _)
  -> { bs : Data.ByteString.ByteString | 1 <= bslen bs }
  -> _

assume Data.ByteString.foldr1
  :: (_ -> _ -> _)
  -> { bs : Data.ByteString.ByteString | 1 <= bslen bs }
  -> _

assume Data.ByteString.foldr1'
  :: (_ -> _ -> _)
  -> { bs : Data.ByteString.ByteString | 1 <= bslen bs }
  -> _

assume Data.ByteString.concat
  :: is : [Data.ByteString.ByteString]
  -> { o : Data.ByteString.ByteString | (len is == 0) ==> (bslen o == 0) }

assume Data.ByteString.concatMap
  :: (_ -> Data.ByteString.ByteString)
  -> i : Data.ByteString.ByteString
  -> { o : Data.ByteString.ByteString | bslen i == 0 ==> bslen o == 0 }

assume Data.ByteString.any
  :: (_ -> GHC.Types.Bool)
  -> bs : Data.ByteString.ByteString
  -> { b : GHC.Types.Bool | bslen bs == 0 ==> not b }

assume Data.ByteString.all
  :: (_ -> GHC.Types.Bool)
  -> bs : Data.ByteString.ByteString
  -> { b : GHC.Types.Bool | bslen bs == 0 ==> b }

assume Data.ByteString.maximum :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> _

assume Data.ByteString.minimum :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> _

assume Data.ByteString.scanl :: (_ -> _ -> _)
      -> _
      -> i : Data.ByteString.ByteString
      -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume Data.ByteString.scanl1 :: (_ -> _ -> _)
       -> i : { i : Data.ByteString.ByteString | 1 <= bslen i }
       -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume Data.ByteString.scanr
    :: (_ -> _ -> _)
    -> _
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume Data.ByteString.scanr1
    :: (_ -> _ -> _)
    -> i : { i : Data.ByteString.ByteString | 1 <= bslen i }
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume Data.ByteString.mapAccumL
    :: (acc -> _ -> (acc, _))
    -> acc
    -> i : Data.ByteString.ByteString
    -> (acc, { o : Data.ByteString.ByteString | bslen o == bslen i })

assume Data.ByteString.mapAccumR
    :: (acc -> _ -> (acc, _))
    -> acc
    -> i : Data.ByteString.ByteString
    -> (acc, { o : Data.ByteString.ByteString | bslen o == bslen i })

assume Data.ByteString.replicate
    :: n : Int
    -> _
    -> { bs : Data.ByteString.ByteString | bslen bs == n }

assume Data.ByteString.unfoldrN
    :: n : Int
    -> (a -> Maybe (_, a))
    -> a
    -> ({ bs : Data.ByteString.ByteString | bslen bs <= n }, Maybe a)

assume Data.ByteString.take
    :: n : Int
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | (n <= 0 <=> bslen o == 0) &&
                                          ((0 <= n && n <= bslen i) <=> bslen o == n) &&
                                          (bslen i <= n <=> bslen o = bslen i) }

assume Data.ByteString.drop
    :: n : Int
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | (n <= 0 <=> bslen o == bslen i) &&
                                          ((0 <= n && n <= bslen i) <=> bslen o == bslen i - n) &&
                                          (bslen i <= n <=> bslen o == 0) }

assume Data.ByteString.splitAt
    :: n : Int
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | (n <= 0 <=> bslen l == 0) &&
                                            ((0 <= n && n <= bslen i) <=> bslen l == n) &&
                                            (bslen i <= n <=> bslen l == bslen i) }
       , { r : Data.ByteString.ByteString | (n <= 0 <=> bslen r == bslen i) &&
                                            ((0 <= n && n <= bslen i) <=> bslen r == bslen i - n) &&
                                            (bslen i <= n <=> bslen r == 0) }
       )

assume Data.ByteString.takeWhile
    :: (_ -> GHC.Types.Bool)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o <= bslen i }

assume Data.ByteString.dropWhile
    :: (_ -> GHC.Types.Bool)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o <= bslen i }

assume Data.ByteString.span
    :: (_ -> GHC.Types.Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

assume Data.ByteString.spanEnd
    :: (_ -> GHC.Types.Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

assume Data.ByteString.break
    :: (_ -> GHC.Types.Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

assume Data.ByteString.breakEnd
    :: (_ -> GHC.Types.Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

assume Data.ByteString.group
    :: i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | 1 <= bslen o && bslen o <= bslen i }]

assume Data.ByteString.groupBy
    :: (_ -> _ -> GHC.Types.Bool)
    -> i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | 1 <= bslen o && bslen o <= bslen i }]

assume Data.ByteString.inits
    :: i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | bslen o <= bslen i }]

assume Data.ByteString.tails
    :: i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | bslen o <= bslen i }]

assume Data.ByteString.split
    :: _
    -> i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | bslen o <= bslen i }]

assume Data.ByteString.splitWith
    :: (_ -> GHC.Types.Bool)
    -> i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | bslen o <= bslen i }]

assume Data.ByteString.isPrefixOf
    :: l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { b : GHC.Types.Bool | bslen l >= bslen r ==> not b }

assume Data.ByteString.isSuffixOf
    :: l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { b : GHC.Types.Bool | bslen l > bslen r ==> not b }

assume Data.ByteString.isInfixOf
    :: l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { b : GHC.Types.Bool | bslen l > bslen r ==> not b }

assume Data.ByteString.breakSubstring
    :: il : Data.ByteString.ByteString
    -> ir : Data.ByteString.ByteString
    -> ( { ol : Data.ByteString.ByteString | bslen ol <= bslen ir && (bslen il > bslen ir ==> bslen ol == bslen ir)}
       , { or : Data.ByteString.ByteString | bslen or <= bslen ir && (bslen il > bslen ir ==> bslen or == 0) }
       )

assume Data.ByteString.elem
    :: _
    -> bs : Data.ByteString.ByteString
    -> { b : GHC.Types.Bool | bslen bs == 0 ==> not b }

assume Data.ByteString.notElem
    :: _
    -> bs : Data.ByteString.ByteString
    -> { b : GHC.Types.Bool | bslen bs == 0 ==> b }

assume Data.ByteString.find
    :: (_ -> GHC.Types.Bool)
    -> bs : Data.ByteString.ByteString
    -> (Maybe { w8 : _ | bslen bs /= 0 })

assume Data.ByteString.filter
    :: (_ -> GHC.Types.Bool)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o <= bslen i }

assume Data.ByteString.partition
    :: (Word8 -> GHC.Types.Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

assume Data.ByteString.index :: bs : Data.ByteString.ByteString -> { n : Int | 0 <= n && n < bslen bs } -> _

assume Data.ByteString.elemIndex
    :: _
    -> bs : Data.ByteString.ByteString
    -> (Maybe { n : Int | 0 <= n && n < bslen bs })

assume Data.ByteString.elemIndices
    :: _
    -> bs : Data.ByteString.ByteString
    -> [{ n : Int | 0 <= n && n < bslen bs }]

assume Data.ByteString.elemIndexEnd
    :: _
    -> bs : Data.ByteString.ByteString
    -> (Maybe { n : Int | 0 <= n && n < bslen bs })

assume Data.ByteString.findIndex
    :: (_ -> GHC.Types.Bool)
    -> bs : Data.ByteString.ByteString
    -> (Maybe { n : Int | 0 <= n && n < bslen bs })

assume Data.ByteString.findIndices
    :: (_ -> GHC.Types.Bool)
    -> bs : Data.ByteString.ByteString
    -> [{ n : Int | 0 <= n && n < bslen bs }]

assume Data.ByteString.count
    :: _
    -> bs : Data.ByteString.ByteString
    -> { n : Int | 0 <= n && n < bslen bs }

assume Data.ByteString.zip
    :: l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { o : [(_, _)] | len o <= bslen l && len o <= bslen r }

assume Data.ByteString.zipWith
    :: (_ -> _ -> a)
    -> l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { o : [a] | len o <= bslen l && len o <= bslen r }

assume Data.ByteString.unzip
    :: i : [(_, _)]
    -> ( { l : Data.ByteString.ByteString | bslen l == len i }
       , { r : Data.ByteString.ByteString | bslen r == len i }
       )

assume Data.ByteString.sort
    :: i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume Data.ByteString.copy
    :: i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume Data.ByteString.hGet
    :: _
    -> n : { n : Int | 0 <= n }
    -> (IO { bs : Data.ByteString.ByteString | bslen bs == n || bslen bs == 0 })

assume Data.ByteString.hGetSome
    :: _
    -> n : { n : Int | 0 <= n }
    -> (IO { bs : Data.ByteString.ByteString | bslen bs <= n })

assume Data.ByteString.hGetNonBlocking
    :: _
    -> n : { n : Int | 0 <= n }
    -> (IO { bs : Data.ByteString.ByteString | bslen bs <= n })

assume Data.ByteString.uncons
    :: i : Data.ByteString.ByteString
    -> (Maybe (_, { o : Data.ByteString.ByteString | bslen o == bslen i - 1 }))
@-}
