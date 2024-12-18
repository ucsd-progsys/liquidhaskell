{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Data.ByteString.Char8_LHAssumptions where

import Data.ByteString_LHAssumptions()
import Data.ByteString
import Data.ByteString.Char8
import GHC.Types

{-@

assume Data.ByteString.Char8.singleton
    :: GHC.Types.Char -> { bs : ByteString | bslen bs == 1 }

assume Data.ByteString.Char8.pack
    :: w8s : [GHC.Types.Char]
    -> { bs : ByteString | bslen bs == len w8s }

assume Data.ByteString.Char8.unpack
    :: bs : ByteString
    -> { w8s : [GHC.Types.Char] | len w8s == bslen bs }

assume Data.ByteString.Char8.cons
    :: GHC.Types.Char
    -> i : ByteString
    -> { o : ByteString | bslen o == bslen i + 1 }

assume Data.ByteString.Char8.snoc
    :: i : ByteString
    -> GHC.Types.Char
    -> { o : ByteString | bslen o == bslen i + 1 }

assume Data.ByteString.Char8.head :: { bs : ByteString | 1 <= bslen bs } -> GHC.Types.Char

assume Data.ByteString.Char8.uncons
    :: i : ByteString
    -> Maybe (GHC.Types.Char, { o : ByteString | bslen o == bslen i - 1 })

assume Data.ByteString.Char8.unsnoc
    :: i : ByteString
    -> Maybe ({ o : ByteString | bslen o == bslen i - 1 }, GHC.Types.Char)

assume Data.ByteString.Char8.last :: { bs : ByteString | 1 <= bslen bs } -> GHC.Types.Char

assume Data.ByteString.Char8.map
    :: (GHC.Types.Char -> GHC.Types.Char)
    -> i : ByteString
    -> { o : ByteString | bslen o == bslen i }

assume Data.ByteString.Char8.intersperse
    :: GHC.Types.Char
    -> i : ByteString
    -> { o : ByteString | (bslen i == 0 <=> bslen o == 0) && (1 <= bslen i <=> bslen o == 2 * bslen i - 1) }

assume Data.ByteString.Char8.foldl1
    :: (GHC.Types.Char -> GHC.Types.Char -> GHC.Types.Char)
    -> { bs : ByteString | 1 <= bslen bs }
    -> Char

assume Data.ByteString.Char8.foldl1'
    :: (GHC.Types.Char -> GHC.Types.Char -> GHC.Types.Char)
    -> { bs : ByteString | 1 <= bslen bs }
    -> GHC.Types.Char

assume Data.ByteString.Char8.foldr1
    :: (GHC.Types.Char -> GHC.Types.Char -> GHC.Types.Char)
    -> { bs : ByteString | 1 <= bslen bs }
    -> Char

assume Data.ByteString.Char8.foldr1'
    :: (GHC.Types.Char -> GHC.Types.Char -> GHC.Types.Char)
    -> { bs : ByteString | 1 <= bslen bs }
    -> GHC.Types.Char

assume Data.ByteString.Char8.concatMap
    :: (GHC.Types.Char -> ByteString)
    -> i : ByteString
    -> { o : ByteString | bslen i == 0 ==> bslen o == 0 }

assume Data.ByteString.Char8.any :: (GHC.Types.Char -> GHC.Types.Bool)
    -> bs : ByteString
    -> { b : GHC.Types.Bool | bslen bs == 0 ==> not b }

assume Data.ByteString.Char8.all :: (GHC.Types.Char -> GHC.Types.Bool)
    -> bs : ByteString
    -> { b : GHC.Types.Bool | bslen bs == 0 ==> b }

assume Data.ByteString.Char8.maximum
    :: { bs : ByteString | 1 <= bslen bs } -> GHC.Types.Char

assume Data.ByteString.Char8.minimum
    :: { bs : ByteString | 1 <= bslen bs } -> GHC.Types.Char

assume Data.ByteString.Char8.scanl
    :: (GHC.Types.Char -> GHC.Types.Char -> GHC.Types.Char)
    -> GHC.Types.Char
    -> i : ByteString
    -> { o : ByteString | bslen o == bslen i }

assume Data.ByteString.Char8.scanl1
    :: (GHC.Types.Char -> GHC.Types.Char -> GHC.Types.Char)
    -> i : { i : ByteString | 1 <= bslen i }
    -> { o : ByteString | bslen o == bslen i }

assume Data.ByteString.Char8.scanr
    :: (GHC.Types.Char -> GHC.Types.Char -> GHC.Types.Char)
    -> GHC.Types.Char
    -> i : ByteString
    -> { o : ByteString | bslen o == bslen i }

assume Data.ByteString.Char8.scanr1
    :: (GHC.Types.Char -> GHC.Types.Char -> GHC.Types.Char)
    -> i : { i : ByteString | 1 <= bslen i }
    -> { o : ByteString | bslen o == bslen i }

assume Data.ByteString.Char8.mapAccumL
    :: (acc -> GHC.Types.Char -> (acc, GHC.Types.Char))
    -> acc
    -> i : ByteString
    -> (acc, { o : ByteString | bslen o == bslen i })

assume Data.ByteString.Char8.mapAccumR
    :: (acc -> GHC.Types.Char -> (acc, GHC.Types.Char))
    -> acc
    -> i : ByteString
    -> (acc, { o : ByteString | bslen o == bslen i })

assume Data.ByteString.Char8.replicate
    :: n : Int
    -> GHC.Types.Char
    -> { bs : ByteString | bslen bs == n }

assume Data.ByteString.Char8.unfoldrN
    :: n : Int
    -> (a -> Maybe (GHC.Types.Char, a))
    -> a
    -> ({ bs : ByteString | bslen bs <= n }, Maybe a)

assume Data.ByteString.Char8.takeWhile
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> i : ByteString
    -> { o : ByteString | bslen o <= bslen i }

assume Data.ByteString.Char8.dropWhile
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> i : ByteString
    -> { o : ByteString | bslen o <= bslen i }

assume Data.ByteString.Char8.span
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> i : ByteString
    -> ( { l : ByteString | bslen l <= bslen i }
       , { r : ByteString | bslen r <= bslen i }
       )

assume Data.ByteString.Char8.spanEnd
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> i : ByteString
    -> ( { l : ByteString | bslen l <= bslen i }
       , { r : ByteString | bslen r <= bslen i }
       )

assume Data.ByteString.Char8.break
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> i : ByteString
    -> ( { l : ByteString | bslen l <= bslen i }
       , { r : ByteString | bslen r <= bslen i }
       )

assume Data.ByteString.Char8.breakEnd
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> i : ByteString
    -> ( { l : ByteString | bslen l <= bslen i }
       , { r : ByteString | bslen r <= bslen i }
       )

assume Data.ByteString.Char8.groupBy
    :: (GHC.Types.Char -> GHC.Types.Char -> GHC.Types.Bool)
    -> i : ByteString
    -> [{ o : ByteString | 1 <= bslen o && bslen o <= bslen i }]

assume Data.ByteString.Char8.split
    :: GHC.Types.Char
    -> i : ByteString
    -> [{ o : ByteString | bslen o <= bslen i }]

assume Data.ByteString.Char8.splitWith
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> i : ByteString
    -> [{ o : ByteString | bslen o <= bslen i }]

assume Data.ByteString.Char8.lines
    :: i : ByteString
    -> [{ o : ByteString | bslen o <= bslen i }]

assume Data.ByteString.Char8.words
    :: i : ByteString
    -> [{ o : ByteString | bslen o <= bslen i }]

assume Data.ByteString.Char8.unlines
    :: is : [ByteString]
    -> { o : ByteString | (len is == 0 <=> bslen o == 0) && bslen o >= len is }

assume Data.ByteString.Char8.unwords
    :: is : [ByteString]
    -> { o : ByteString | (len is == 0 ==> bslen o == 0) && (1 <= len is ==> bslen o >= len is - 1) }

assume Data.ByteString.Char8.elem
    :: GHC.Types.Char
    -> bs : ByteString
    -> { b : GHC.Types.Bool | bslen bs == 0 ==> not b }

assume Data.ByteString.Char8.notElem
    :: GHC.Types.Char
    -> bs : ByteString
    -> { b : GHC.Types.Bool | bslen bs == 0 ==> b }

assume Data.ByteString.Char8.find
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> bs : ByteString
    -> Maybe { w8 : GHC.Types.Char | bslen bs /= 0 }

assume Data.ByteString.Char8.filter
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> i : ByteString
    -> { o : ByteString | bslen o <= bslen i }

assume Data.ByteString.Char8.index
    :: bs : ByteString
    -> { n : Int | 0 <= n && n < bslen bs }
    -> GHC.Types.Char

assume Data.ByteString.Char8.elemIndex
    :: GHC.Types.Char
    -> bs : ByteString
    -> Maybe { n : Int | 0 <= n && n < bslen bs }

assume Data.ByteString.Char8.elemIndices
    :: GHC.Types.Char
    -> bs : ByteString
    -> [{ n : Int | 0 <= n && n < bslen bs }]

assume Data.ByteString.Char8.elemIndexEnd
    :: GHC.Types.Char
    -> bs : ByteString
    -> Maybe { n : Int | 0 <= n && n < bslen bs }

assume Data.ByteString.Char8.findIndex
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> bs : ByteString
    -> Maybe { n : Int | 0 <= n && n < bslen bs }

assume Data.ByteString.Char8.findIndices
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> bs : ByteString
    -> [{ n : Int | 0 <= n && n < bslen bs }]

assume Data.ByteString.Char8.count
    :: GHC.Types.Char
    -> bs : ByteString
    -> { n : Int | 0 <= n && n < bslen bs }

assume Data.ByteString.Char8.zip
    :: l : ByteString
    -> r : ByteString
    -> { o : [(GHC.Types.Char, GHC.Types.Char)] | len o <= bslen l && len o <= bslen r }

assume Data.ByteString.Char8.zipWith
    :: (GHC.Types.Char -> GHC.Types.Char -> a)
    -> l : ByteString
    -> r : ByteString
    -> { o : [a] | len o <= bslen l && len o <= bslen r }

assume Data.ByteString.Char8.unzip
    :: i : [(GHC.Types.Char, GHC.Types.Char)]
    -> ( { l : ByteString | bslen l == len i }
       , { r : ByteString | bslen r == len i }
       )

assume readInt
    :: i : ByteString
    -> Maybe { p : (Int, { o : ByteString | bslen o < bslen i}) | bslen i /= 0 }

assume readInteger
    :: i : ByteString
    -> Maybe { p : (Integer, { o : ByteString | bslen o < bslen i}) | bslen i /= 0 }
@-}
