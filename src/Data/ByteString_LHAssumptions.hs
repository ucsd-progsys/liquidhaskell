{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Data.ByteString_LHAssumptions where

import Data.ByteString
import Data.String_LHAssumptions()
import GHC.Word

{-@
measure bslen :: ByteString -> { n : Int | 0 <= n }

invariant { bs : ByteString  | 0 <= bslen bs }

invariant { bs : ByteString | bslen bs == stringlen bs }

assume empty :: { bs : ByteString | bslen bs == 0 }

assume Data.ByteString.singleton :: _ -> { bs : ByteString | bslen bs == 1 }

assume Data.ByteString.pack :: w8s : [_]
     -> { bs : ByteString | bslen bs == len w8s }

assume Data.ByteString.unpack :: bs : ByteString
       -> { w8s : [_] | len w8s == bslen bs }

assume Data.ByteString.cons :: _
     -> i : ByteString
     -> { o : ByteString | bslen o == bslen i + 1 }

assume Data.ByteString.snoc :: i : ByteString
     -> _
     -> { o : ByteString | bslen o == bslen i + 1 }

assume Data.ByteString.append :: l : ByteString
       -> r : ByteString
       -> { o : ByteString | bslen o == bslen l + bslen r }

assume Data.ByteString.head :: { bs : ByteString | 1 <= bslen bs } -> _

assume Data.ByteString.unsnoc :: i:ByteString
       -> (Maybe ({ o : ByteString | bslen o == bslen i - 1 }, _))

assume Data.ByteString.last :: { bs : ByteString | 1 <= bslen bs } -> _

assume Data.ByteString.tail :: { bs : ByteString | 1 <= bslen bs } -> _

assume Data.ByteString.init
  :: {i:ByteString | 1 <= bslen i }
  -> {o:ByteString | bslen o == bslen i - 1 }

assume Data.ByteString.null
  :: bs : ByteString
  -> { b : Bool | b <=> bslen bs == 0 }

assume Data.ByteString.length :: bs : ByteString -> { n : Int | bslen bs == n }

assume Data.ByteString.map
  :: (_ -> _)
  -> i : ByteString
  -> { o : ByteString | bslen o == bslen i }

assume Data.ByteString.reverse
  :: i : ByteString
  -> { o : ByteString | bslen o == bslen i }

assume Data.ByteString.intersperse
  :: _
  -> i : ByteString
  -> { o : ByteString | (bslen i == 0 <=> bslen o == 0) && (1 <= bslen i <=> bslen o == 2 * bslen i - 1) }

assume Data.ByteString.intercalate
  :: l : ByteString
  -> rs : [ByteString]
  -> { o : ByteString | len rs == 0 ==> bslen o == 0 }

assume Data.ByteString.transpose
  :: is : [ByteString]
  -> { os : [{ bs : ByteString | bslen bs <= len is }] | len is == 0 ==> len os == 0}

assume Data.ByteString.foldl1
  :: (_ -> _ -> _)
  -> { bs : ByteString | 1 <= bslen bs }
  -> _

assume Data.ByteString.foldl1'
  :: (_ -> _ -> _)
  -> { bs : ByteString | 1 <= bslen bs }
  -> _

assume Data.ByteString.foldr1
  :: (_ -> _ -> _)
  -> { bs : ByteString | 1 <= bslen bs }
  -> _

assume Data.ByteString.foldr1'
  :: (_ -> _ -> _)
  -> { bs : ByteString | 1 <= bslen bs }
  -> _

assume Data.ByteString.concat
  :: is : [ByteString]
  -> { o : ByteString | (len is == 0) ==> (bslen o == 0) }

assume Data.ByteString.concatMap
  :: (_ -> ByteString)
  -> i : ByteString
  -> { o : ByteString | bslen i == 0 ==> bslen o == 0 }

assume Data.ByteString.any
  :: (_ -> Bool)
  -> bs : ByteString
  -> { b : Bool | bslen bs == 0 ==> not b }

assume Data.ByteString.all
  :: (_ -> Bool)
  -> bs : ByteString
  -> { b : Bool | bslen bs == 0 ==> b }

assume Data.ByteString.maximum :: { bs : ByteString | 1 <= bslen bs } -> _

assume Data.ByteString.minimum :: { bs : ByteString | 1 <= bslen bs } -> _

assume Data.ByteString.scanl :: (_ -> _ -> _)
      -> _
      -> i : ByteString
      -> { o : ByteString | bslen o == bslen i }

assume Data.ByteString.scanl1 :: (_ -> _ -> _)
       -> i : { i : ByteString | 1 <= bslen i }
       -> { o : ByteString | bslen o == bslen i }

assume Data.ByteString.scanr
    :: (_ -> _ -> _)
    -> _
    -> i : ByteString
    -> { o : ByteString | bslen o == bslen i }

assume Data.ByteString.scanr1
    :: (_ -> _ -> _)
    -> i : { i : ByteString | 1 <= bslen i }
    -> { o : ByteString | bslen o == bslen i }

assume Data.ByteString.mapAccumL
    :: (acc -> _ -> (acc, _))
    -> acc
    -> i : ByteString
    -> (acc, { o : ByteString | bslen o == bslen i })

assume Data.ByteString.mapAccumR
    :: (acc -> _ -> (acc, _))
    -> acc
    -> i : ByteString
    -> (acc, { o : ByteString | bslen o == bslen i })

assume Data.ByteString.replicate
    :: n : Int
    -> _
    -> { bs : ByteString | bslen bs == n }

assume Data.ByteString.unfoldrN
    :: n : Int
    -> (a -> Maybe (_, a))
    -> a
    -> ({ bs : ByteString | bslen bs <= n }, Maybe a)

assume Data.ByteString.take
    :: n : Int
    -> i : ByteString
    -> { o : ByteString | (n <= 0 <=> bslen o == 0) &&
                                          ((0 <= n && n <= bslen i) <=> bslen o == n) &&
                                          (bslen i <= n <=> bslen o = bslen i) }

assume Data.ByteString.drop
    :: n : Int
    -> i : ByteString
    -> { o : ByteString | (n <= 0 <=> bslen o == bslen i) &&
                                          ((0 <= n && n <= bslen i) <=> bslen o == bslen i - n) &&
                                          (bslen i <= n <=> bslen o == 0) }

assume Data.ByteString.splitAt
    :: n : Int
    -> i : ByteString
    -> ( { l : ByteString | (n <= 0 <=> bslen l == 0) &&
                                            ((0 <= n && n <= bslen i) <=> bslen l == n) &&
                                            (bslen i <= n <=> bslen l == bslen i) }
       , { r : ByteString | (n <= 0 <=> bslen r == bslen i) &&
                                            ((0 <= n && n <= bslen i) <=> bslen r == bslen i - n) &&
                                            (bslen i <= n <=> bslen r == 0) }
       )

assume Data.ByteString.takeWhile
    :: (_ -> Bool)
    -> i : ByteString
    -> { o : ByteString | bslen o <= bslen i }

assume Data.ByteString.dropWhile
    :: (_ -> Bool)
    -> i : ByteString
    -> { o : ByteString | bslen o <= bslen i }

assume Data.ByteString.span
    :: (_ -> Bool)
    -> i : ByteString
    -> ( { l : ByteString | bslen l <= bslen i }
       , { r : ByteString | bslen r <= bslen i }
       )

assume Data.ByteString.spanEnd
    :: (_ -> Bool)
    -> i : ByteString
    -> ( { l : ByteString | bslen l <= bslen i }
       , { r : ByteString | bslen r <= bslen i }
       )

assume Data.ByteString.break
    :: (_ -> Bool)
    -> i : ByteString
    -> ( { l : ByteString | bslen l <= bslen i }
       , { r : ByteString | bslen r <= bslen i }
       )

assume Data.ByteString.breakEnd
    :: (_ -> Bool)
    -> i : ByteString
    -> ( { l : ByteString | bslen l <= bslen i }
       , { r : ByteString | bslen r <= bslen i }
       )

assume Data.ByteString.group
    :: i : ByteString
    -> [{ o : ByteString | 1 <= bslen o && bslen o <= bslen i }]

assume Data.ByteString.groupBy
    :: (_ -> _ -> Bool)
    -> i : ByteString
    -> [{ o : ByteString | 1 <= bslen o && bslen o <= bslen i }]

assume Data.ByteString.inits
    :: i : ByteString
    -> [{ o : ByteString | bslen o <= bslen i }]

assume Data.ByteString.tails
    :: i : ByteString
    -> [{ o : ByteString | bslen o <= bslen i }]

assume Data.ByteString.split
    :: _
    -> i : ByteString
    -> [{ o : ByteString | bslen o <= bslen i }]

assume Data.ByteString.splitWith
    :: (_ -> Bool)
    -> i : ByteString
    -> [{ o : ByteString | bslen o <= bslen i }]

assume Data.ByteString.isPrefixOf
    :: l : ByteString
    -> r : ByteString
    -> { b : Bool | bslen l >= bslen r ==> not b }

assume Data.ByteString.isSuffixOf
    :: l : ByteString
    -> r : ByteString
    -> { b : Bool | bslen l > bslen r ==> not b }

assume Data.ByteString.isInfixOf
    :: l : ByteString
    -> r : ByteString
    -> { b : Bool | bslen l > bslen r ==> not b }

assume Data.ByteString.breakSubstring
    :: il : ByteString
    -> ir : ByteString
    -> ( { ol : ByteString | bslen ol <= bslen ir && (bslen il > bslen ir ==> bslen ol == bslen ir)}
       , { or : ByteString | bslen or <= bslen ir && (bslen il > bslen ir ==> bslen or == 0) }
       )

assume Data.ByteString.elem
    :: _
    -> bs : ByteString
    -> { b : Bool | bslen bs == 0 ==> not b }

assume Data.ByteString.notElem
    :: _
    -> bs : ByteString
    -> { b : Bool | bslen bs == 0 ==> b }

assume Data.ByteString.find
    :: (_ -> Bool)
    -> bs : ByteString
    -> (Maybe { w8 : _ | bslen bs /= 0 })

assume Data.ByteString.filter
    :: (_ -> Bool)
    -> i : ByteString
    -> { o : ByteString | bslen o <= bslen i }

assume Data.ByteString.partition
    :: (Word8 -> Bool)
    -> i : ByteString
    -> ( { l : ByteString | bslen l <= bslen i }
       , { r : ByteString | bslen r <= bslen i }
       )

assume Data.ByteString.index :: bs : ByteString -> { n : Int | 0 <= n && n < bslen bs } -> _

assume Data.ByteString.elemIndex
    :: _
    -> bs : ByteString
    -> (Maybe { n : Int | 0 <= n && n < bslen bs })

assume Data.ByteString.elemIndices
    :: _
    -> bs : ByteString
    -> [{ n : Int | 0 <= n && n < bslen bs }]

assume Data.ByteString.elemIndexEnd
    :: _
    -> bs : ByteString
    -> (Maybe { n : Int | 0 <= n && n < bslen bs })

assume Data.ByteString.findIndex
    :: (_ -> Bool)
    -> bs : ByteString
    -> (Maybe { n : Int | 0 <= n && n < bslen bs })

assume Data.ByteString.findIndices
    :: (_ -> Bool)
    -> bs : ByteString
    -> [{ n : Int | 0 <= n && n < bslen bs }]

assume Data.ByteString.count
    :: _
    -> bs : ByteString
    -> { n : Int | 0 <= n && n < bslen bs }

assume Data.ByteString.zip
    :: l : ByteString
    -> r : ByteString
    -> { o : [(_, _)] | len o <= bslen l && len o <= bslen r }

assume Data.ByteString.zipWith
    :: (_ -> _ -> a)
    -> l : ByteString
    -> r : ByteString
    -> { o : [a] | len o <= bslen l && len o <= bslen r }

assume Data.ByteString.unzip
    :: i : [(_, _)]
    -> ( { l : ByteString | bslen l == len i }
       , { r : ByteString | bslen r == len i }
       )

assume Data.ByteString.sort
    :: i : ByteString
    -> { o : ByteString | bslen o == bslen i }

assume Data.ByteString.copy
    :: i : ByteString
    -> { o : ByteString | bslen o == bslen i }

assume Data.ByteString.hGet
    :: _
    -> n : { n : Int | 0 <= n }
    -> (IO { bs : ByteString | bslen bs == n || bslen bs == 0 })

assume Data.ByteString.hGetSome
    :: _
    -> n : { n : Int | 0 <= n }
    -> (IO { bs : ByteString | bslen bs <= n })

assume Data.ByteString.hGetNonBlocking
    :: _
    -> n : { n : Int | 0 <= n }
    -> (IO { bs : ByteString | bslen bs <= n })

assume Data.ByteString.uncons
    :: i : ByteString
    -> (Maybe (_, { o : ByteString | bslen o == bslen i - 1 }))
@-}
