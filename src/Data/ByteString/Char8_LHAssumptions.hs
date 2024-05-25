{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Data.ByteString.Char8_LHAssumptions where

import Data.ByteString_LHAssumptions()
import Data.ByteString
import Data.ByteString.Char8

{-@

assume Data.ByteString.Char8.singleton
    :: GHC.Types.Char -> { bs : Data.ByteString.ByteString | bslen bs == 1 }

assume Data.ByteString.Char8.pack
    :: w8s : [GHC.Types.Char]
    -> { bs : Data.ByteString.ByteString | bslen bs == len w8s }

assume Data.ByteString.Char8.unpack
    :: bs : Data.ByteString.ByteString
    -> { w8s : [GHC.Types.Char] | len w8s == bslen bs }

assume Data.ByteString.Char8.cons
    :: GHC.Types.Char
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i + 1 }

assume Data.ByteString.Char8.snoc
    :: i : Data.ByteString.ByteString
    -> GHC.Types.Char
    -> { o : Data.ByteString.ByteString | bslen o == bslen i + 1 }

assume Data.ByteString.Char8.head :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> GHC.Types.Char

assume Data.ByteString.Char8.uncons
    :: i : Data.ByteString.ByteString
    -> Maybe (GHC.Types.Char, { o : Data.ByteString.ByteString | bslen o == bslen i - 1 })

assume Data.ByteString.Char8.unsnoc
    :: i : Data.ByteString.ByteString
    -> Maybe ({ o : Data.ByteString.ByteString | bslen o == bslen i - 1 }, GHC.Types.Char)

assume Data.ByteString.Char8.last :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> GHC.Types.Char

assume Data.ByteString.Char8.map
    :: (GHC.Types.Char -> GHC.Types.Char)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume Data.ByteString.Char8.intersperse
    :: GHC.Types.Char
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | (bslen i == 0 <=> bslen o == 0) && (1 <= bslen i <=> bslen o == 2 * bslen i - 1) }

assume Data.ByteString.Char8.foldl1
    :: (GHC.Types.Char -> GHC.Types.Char -> GHC.Types.Char)
    -> { bs : Data.ByteString.ByteString | 1 <= bslen bs }
    -> Char

assume Data.ByteString.Char8.foldl1'
    :: (GHC.Types.Char -> GHC.Types.Char -> GHC.Types.Char)
    -> { bs : Data.ByteString.ByteString | 1 <= bslen bs }
    -> GHC.Types.Char

assume Data.ByteString.Char8.foldr1
    :: (GHC.Types.Char -> GHC.Types.Char -> GHC.Types.Char)
    -> { bs : Data.ByteString.ByteString | 1 <= bslen bs }
    -> Char

assume Data.ByteString.Char8.foldr1'
    :: (GHC.Types.Char -> GHC.Types.Char -> GHC.Types.Char)
    -> { bs : Data.ByteString.ByteString | 1 <= bslen bs }
    -> GHC.Types.Char

assume Data.ByteString.Char8.concatMap
    :: (GHC.Types.Char -> Data.ByteString.ByteString)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen i == 0 ==> bslen o == 0 }

assume Data.ByteString.Char8.any :: (GHC.Types.Char -> GHC.Types.Bool)
    -> bs : Data.ByteString.ByteString
    -> { b : GHC.Types.Bool | bslen bs == 0 ==> not b }

assume Data.ByteString.Char8.all :: (GHC.Types.Char -> GHC.Types.Bool)
    -> bs : Data.ByteString.ByteString
    -> { b : GHC.Types.Bool | bslen bs == 0 ==> b }

assume Data.ByteString.Char8.maximum
    :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> GHC.Types.Char

assume Data.ByteString.Char8.minimum
    :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> GHC.Types.Char

assume Data.ByteString.Char8.scanl
    :: (GHC.Types.Char -> GHC.Types.Char -> GHC.Types.Char)
    -> GHC.Types.Char
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume Data.ByteString.Char8.scanl1
    :: (GHC.Types.Char -> GHC.Types.Char -> GHC.Types.Char)
    -> i : { i : Data.ByteString.ByteString | 1 <= bslen i }
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume Data.ByteString.Char8.scanr
    :: (GHC.Types.Char -> GHC.Types.Char -> GHC.Types.Char)
    -> GHC.Types.Char
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume Data.ByteString.Char8.scanr1
    :: (GHC.Types.Char -> GHC.Types.Char -> GHC.Types.Char)
    -> i : { i : Data.ByteString.ByteString | 1 <= bslen i }
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume Data.ByteString.Char8.mapAccumL
    :: (acc -> GHC.Types.Char -> (acc, GHC.Types.Char))
    -> acc
    -> i : Data.ByteString.ByteString
    -> (acc, { o : Data.ByteString.ByteString | bslen o == bslen i })

assume Data.ByteString.Char8.mapAccumR
    :: (acc -> GHC.Types.Char -> (acc, GHC.Types.Char))
    -> acc
    -> i : Data.ByteString.ByteString
    -> (acc, { o : Data.ByteString.ByteString | bslen o == bslen i })

assume Data.ByteString.Char8.replicate
    :: n : Int
    -> GHC.Types.Char
    -> { bs : Data.ByteString.ByteString | bslen bs == n }

assume Data.ByteString.Char8.unfoldrN
    :: n : Int
    -> (a -> Maybe (GHC.Types.Char, a))
    -> a
    -> ({ bs : Data.ByteString.ByteString | bslen bs <= n }, Maybe a)

assume Data.ByteString.Char8.takeWhile
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o <= bslen i }

assume Data.ByteString.Char8.dropWhile
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o <= bslen i }

assume Data.ByteString.Char8.span
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

assume Data.ByteString.Char8.spanEnd
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

assume Data.ByteString.Char8.break
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

assume Data.ByteString.Char8.breakEnd
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

assume Data.ByteString.Char8.groupBy
    :: (GHC.Types.Char -> GHC.Types.Char -> GHC.Types.Bool)
    -> i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | 1 <= bslen o && bslen o <= bslen i }]

assume Data.ByteString.Char8.split
    :: GHC.Types.Char
    -> i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | bslen o <= bslen i }]

assume Data.ByteString.Char8.splitWith
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | bslen o <= bslen i }]

assume Data.ByteString.Char8.lines
    :: i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | bslen o <= bslen i }]

assume Data.ByteString.Char8.words
    :: i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | bslen o <= bslen i }]

assume Data.ByteString.Char8.unlines
    :: is : [Data.ByteString.ByteString]
    -> { o : Data.ByteString.ByteString | (len is == 0 <=> bslen o == 0) && bslen o >= len is }

assume Data.ByteString.Char8.unwords
    :: is : [Data.ByteString.ByteString]
    -> { o : Data.ByteString.ByteString | (len is == 0 ==> bslen o == 0) && (1 <= len is ==> bslen o >= len is - 1) }

assume Data.ByteString.Char8.elem
    :: GHC.Types.Char
    -> bs : Data.ByteString.ByteString
    -> { b : GHC.Types.Bool | bslen bs == 0 ==> not b }

assume Data.ByteString.Char8.notElem
    :: GHC.Types.Char
    -> bs : Data.ByteString.ByteString
    -> { b : GHC.Types.Bool | bslen bs == 0 ==> b }

assume Data.ByteString.Char8.find
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> bs : Data.ByteString.ByteString
    -> Maybe { w8 : GHC.Types.Char | bslen bs /= 0 }

assume Data.ByteString.Char8.filter
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o <= bslen i }

assume Data.ByteString.Char8.index
    :: bs : Data.ByteString.ByteString
    -> { n : Int | 0 <= n && n < bslen bs }
    -> GHC.Types.Char

assume Data.ByteString.Char8.elemIndex
    :: GHC.Types.Char
    -> bs : Data.ByteString.ByteString
    -> Maybe { n : Int | 0 <= n && n < bslen bs }

assume Data.ByteString.Char8.elemIndices
    :: GHC.Types.Char
    -> bs : Data.ByteString.ByteString
    -> [{ n : Int | 0 <= n && n < bslen bs }]

assume Data.ByteString.Char8.elemIndexEnd
    :: GHC.Types.Char
    -> bs : Data.ByteString.ByteString
    -> Maybe { n : Int | 0 <= n && n < bslen bs }

assume Data.ByteString.Char8.findIndex
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> bs : Data.ByteString.ByteString
    -> Maybe { n : Int | 0 <= n && n < bslen bs }

assume Data.ByteString.Char8.findIndices
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> bs : Data.ByteString.ByteString
    -> [{ n : Int | 0 <= n && n < bslen bs }]

assume Data.ByteString.Char8.count
    :: GHC.Types.Char
    -> bs : Data.ByteString.ByteString
    -> { n : Int | 0 <= n && n < bslen bs }

assume Data.ByteString.Char8.zip
    :: l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { o : [(GHC.Types.Char, GHC.Types.Char)] | len o <= bslen l && len o <= bslen r }

assume Data.ByteString.Char8.zipWith
    :: (GHC.Types.Char -> GHC.Types.Char -> a)
    -> l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { o : [a] | len o <= bslen l && len o <= bslen r }

assume Data.ByteString.Char8.unzip
    :: i : [(GHC.Types.Char, GHC.Types.Char)]
    -> ( { l : Data.ByteString.ByteString | bslen l == len i }
       , { r : Data.ByteString.ByteString | bslen r == len i }
       )

assume Data.ByteString.ReadInt.readInt
    :: i : Data.ByteString.ByteString
    -> Maybe { p : (Int, { o : Data.ByteString.ByteString | bslen o < bslen i}) | bslen i /= 0 }

assume Data.ByteString.ReadNat.readInteger
    :: i : Data.ByteString.ByteString
    -> Maybe { p : (Integer, { o : Data.ByteString.ByteString | bslen o < bslen i}) | bslen i /= 0 }
@-}
