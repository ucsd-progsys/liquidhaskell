{-# OPTIONS_GHC -Wno-unused-imports #-}
module Data.ByteString.Char8_LHAssumptions where

import Data.ByteString_LHAssumptions()
import Data.ByteString
import Data.ByteString.Char8

{-@

assume Data.ByteString.Char8.singleton
    :: Char -> { bs : Data.ByteString.ByteString | bslen bs == 1 }

assume Data.ByteString.Char8.pack
    :: w8s : [Char]
    -> { bs : Data.ByteString.ByteString | bslen bs == len w8s }

assume Data.ByteString.Char8.unpack
    :: bs : Data.ByteString.ByteString
    -> { w8s : [Char] | len w8s == bslen bs }

assume Data.ByteString.Char8.cons
    :: Char
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i + 1 }

assume Data.ByteString.Char8.snoc
    :: i : Data.ByteString.ByteString
    -> Char
    -> { o : Data.ByteString.ByteString | bslen o == bslen i + 1 }

assume Data.ByteString.Char8.head :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> Char

assume Data.ByteString.Char8.uncons
    :: i : Data.ByteString.ByteString
    -> Maybe (Char, { o : Data.ByteString.ByteString | bslen o == bslen i - 1 })

assume Data.ByteString.Char8.unsnoc
    :: i : Data.ByteString.ByteString
    -> Maybe ({ o : Data.ByteString.ByteString | bslen o == bslen i - 1 }, Char)

assume Data.ByteString.Char8.last :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> Char

assume Data.ByteString.Char8.map
    :: (Char -> Char)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume Data.ByteString.Char8.intersperse
    :: Char
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | (bslen i == 0 <=> bslen o == 0) && (1 <= bslen i <=> bslen o == 2 * bslen i - 1) }

assume Data.ByteString.Char8.foldl1
    :: (Char -> Char -> Char)
    -> { bs : Data.ByteString.ByteString | 1 <= bslen bs }
    -> Char

assume Data.ByteString.Char8.foldl1'
    :: (Char -> Char -> Char)
    -> { bs : Data.ByteString.ByteString | 1 <= bslen bs }
    -> Char

assume Data.ByteString.Char8.foldr1
    :: (Char -> Char -> Char)
    -> { bs : Data.ByteString.ByteString | 1 <= bslen bs }
    -> Char

assume Data.ByteString.Char8.foldr1'
    :: (Char -> Char -> Char)
    -> { bs : Data.ByteString.ByteString | 1 <= bslen bs }
    -> Char

assume Data.ByteString.Char8.concatMap
    :: (Char -> Data.ByteString.ByteString)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen i == 0 ==> bslen o == 0 }

assume Data.ByteString.Char8.any :: (Char -> GHC.Types.Bool)
    -> bs : Data.ByteString.ByteString
    -> { b : GHC.Types.Bool | bslen bs == 0 ==> not b }

assume Data.ByteString.Char8.all :: (Char -> GHC.Types.Bool)
    -> bs : Data.ByteString.ByteString
    -> { b : GHC.Types.Bool | bslen bs == 0 ==> b }

assume Data.ByteString.Char8.maximum
    :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> Char

assume Data.ByteString.Char8.minimum
    :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> Char

assume Data.ByteString.Char8.scanl
    :: (Char -> Char -> Char)
    -> Char
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume Data.ByteString.Char8.scanl1
    :: (Char -> Char -> Char)
    -> i : { i : Data.ByteString.ByteString | 1 <= bslen i }
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume Data.ByteString.Char8.scanr
    :: (Char -> Char -> Char)
    -> Char
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume Data.ByteString.Char8.scanr1
    :: (Char -> Char -> Char)
    -> i : { i : Data.ByteString.ByteString | 1 <= bslen i }
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

assume Data.ByteString.Char8.mapAccumL
    :: (acc -> Char -> (acc, Char))
    -> acc
    -> i : Data.ByteString.ByteString
    -> (acc, { o : Data.ByteString.ByteString | bslen o == bslen i })

assume Data.ByteString.Char8.mapAccumR
    :: (acc -> Char -> (acc, Char))
    -> acc
    -> i : Data.ByteString.ByteString
    -> (acc, { o : Data.ByteString.ByteString | bslen o == bslen i })

assume Data.ByteString.Char8.replicate
    :: n : Int
    -> Char
    -> { bs : Data.ByteString.ByteString | bslen bs == n }

assume Data.ByteString.Char8.unfoldrN
    :: n : Int
    -> (a -> Maybe (Char, a))
    -> a
    -> ({ bs : Data.ByteString.ByteString | bslen bs <= n }, Maybe a)

assume Data.ByteString.Char8.takeWhile
    :: (Char -> GHC.Types.Bool)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o <= bslen i }

assume Data.ByteString.Char8.dropWhile
    :: (Char -> GHC.Types.Bool)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o <= bslen i }

assume Data.ByteString.Char8.span
    :: (Char -> GHC.Types.Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

assume Data.ByteString.Char8.spanEnd
    :: (Char -> GHC.Types.Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

assume Data.ByteString.Char8.break
    :: (Char -> GHC.Types.Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

assume Data.ByteString.Char8.breakEnd
    :: (Char -> GHC.Types.Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

assume Data.ByteString.Char8.groupBy
    :: (Char -> Char -> GHC.Types.Bool)
    -> i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | 1 <= bslen o && bslen o <= bslen i }]

assume Data.ByteString.Char8.split
    :: Char
    -> i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | bslen o <= bslen i }]

assume Data.ByteString.Char8.splitWith
    :: (Char -> GHC.Types.Bool)
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
    :: Char
    -> bs : Data.ByteString.ByteString
    -> { b : GHC.Types.Bool | bslen bs == 0 ==> not b }

assume Data.ByteString.Char8.notElem
    :: Char
    -> bs : Data.ByteString.ByteString
    -> { b : GHC.Types.Bool | bslen bs == 0 ==> b }

assume Data.ByteString.Char8.find
    :: (Char -> GHC.Types.Bool)
    -> bs : Data.ByteString.ByteString
    -> Maybe { w8 : Char | bslen bs /= 0 }

assume Data.ByteString.Char8.filter
    :: (Char -> GHC.Types.Bool)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o <= bslen i }

assume Data.ByteString.Char8.index
    :: bs : Data.ByteString.ByteString
    -> { n : Int | 0 <= n && n < bslen bs }
    -> Char

assume Data.ByteString.Char8.elemIndex
    :: Char
    -> bs : Data.ByteString.ByteString
    -> Maybe { n : Int | 0 <= n && n < bslen bs }

assume Data.ByteString.Char8.elemIndices
    :: Char
    -> bs : Data.ByteString.ByteString
    -> [{ n : Int | 0 <= n && n < bslen bs }]

assume Data.ByteString.Char8.elemIndexEnd
    :: Char
    -> bs : Data.ByteString.ByteString
    -> Maybe { n : Int | 0 <= n && n < bslen bs }

assume Data.ByteString.Char8.findIndex
    :: (Char -> GHC.Types.Bool)
    -> bs : Data.ByteString.ByteString
    -> Maybe { n : Int | 0 <= n && n < bslen bs }

assume Data.ByteString.Char8.findIndices
    :: (Char -> GHC.Types.Bool)
    -> bs : Data.ByteString.ByteString
    -> [{ n : Int | 0 <= n && n < bslen bs }]

assume Data.ByteString.Char8.count
    :: Char
    -> bs : Data.ByteString.ByteString
    -> { n : Int | 0 <= n && n < bslen bs }

assume Data.ByteString.Char8.zip
    :: l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { o : [(Char, Char)] | len o <= bslen l && len o <= bslen r }

assume Data.ByteString.Char8.zipWith
    :: (Char -> Char -> a)
    -> l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { o : [a] | len o <= bslen l && len o <= bslen r }

assume Data.ByteString.Char8.unzip
    :: i : [(Char, Char)]
    -> ( { l : Data.ByteString.ByteString | bslen l == len i }
       , { r : Data.ByteString.ByteString | bslen r == len i }
       )

assume Data.ByteString.Char8.readInt
    :: i : Data.ByteString.ByteString
    -> Maybe { p : (Int, { o : Data.ByteString.ByteString | bslen o < bslen i}) | bslen i /= 0 }

assume Data.ByteString.Char8.readInteger
    :: i : Data.ByteString.ByteString
    -> Maybe { p : (Integer, { o : Data.ByteString.ByteString | bslen o < bslen i}) | bslen i /= 0 }
@-}
