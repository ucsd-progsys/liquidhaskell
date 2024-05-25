{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Data.ByteString.Lazy.Char8_LHAssumptions where

import Data.ByteString.Lazy hiding (hGetNonBlocking, scanl)
import Data.ByteString.Lazy.Char8
import Data.ByteString.Lazy_LHAssumptions()

{-@
assume Data.ByteString.Lazy.Char8.last :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs } -> GHC.Types.Char

assume Data.ByteString.Lazy.Char8.singleton
    :: GHC.Types.Char -> { bs : Data.ByteString.Lazy.ByteString | bllen bs == 1 }

assume Data.ByteString.Lazy.Char8.pack
    :: w8s : [GHC.Types.Char]
    -> { bs : Data.ByteString.Lazy.ByteString | bllen bs == len w8s }

assume Data.ByteString.Lazy.Char8.unpack
    :: bs : Data.ByteString.Lazy.ByteString
    -> { w8s : [GHC.Types.Char] | len w8s == bllen bs }

assume Data.ByteString.Lazy.Char8.cons
    :: GHC.Types.Char
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i + 1 }

assume Data.ByteString.Lazy.Char8.snoc
    :: i : Data.ByteString.Lazy.ByteString
    -> GHC.Types.Char
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i + 1 }

assume Data.ByteString.Lazy.Char8.head
    :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> GHC.Types.Char

assume Data.ByteString.Lazy.Char8.uncons
    :: i : Data.ByteString.Lazy.ByteString
    -> Maybe (GHC.Types.Char, { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i - 1 })

assume Data.ByteString.Lazy.Char8.unsnoc
    :: i : Data.ByteString.Lazy.ByteString
    -> Maybe ({ o : Data.ByteString.Lazy.ByteString | bllen o == bllen i - 1 }, GHC.Types.Char)

assume Data.ByteString.Lazy.Char8.map
    :: (GHC.Types.Char -> GHC.Types.Char)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume Data.ByteString.Lazy.Char8.intersperse
    :: GHC.Types.Char
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | (bllen i == 0 <=> bllen o == 0) && (1 <= bllen i <=> bllen o == 2 * bllen i - 1) }

assume Data.ByteString.Lazy.Char8.foldl1
    :: (GHC.Types.Char -> GHC.Types.Char -> GHC.Types.Char)
    -> { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> GHC.Types.Char

assume Data.ByteString.Lazy.Char8.foldl1'
    :: (GHC.Types.Char -> GHC.Types.Char -> GHC.Types.Char)
    -> { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> GHC.Types.Char

assume Data.ByteString.Lazy.Char8.foldr1
    :: (GHC.Types.Char -> GHC.Types.Char -> GHC.Types.Char)
    -> { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> GHC.Types.Char

assume Data.ByteString.Lazy.Char8.concatMap
    :: (GHC.Types.Char -> Data.ByteString.Lazy.ByteString)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen i == 0 ==> bllen o == 0 }

assume Data.ByteString.Lazy.Char8.any :: (GHC.Types.Char -> GHC.Types.Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> { b : GHC.Types.Bool | bllen bs == 0 ==> not b }

assume Data.ByteString.Lazy.Char8.all :: (GHC.Types.Char -> GHC.Types.Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> { b : GHC.Types.Bool | bllen bs == 0 ==> b }

assume Data.ByteString.Lazy.Char8.maximum :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs } -> GHC.Types.Char

assume Data.ByteString.Lazy.Char8.minimum :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs } -> GHC.Types.Char

assume Data.ByteString.Lazy.Char8.scanl
    :: (GHC.Types.Char -> GHC.Types.Char -> GHC.Types.Char)
    -> GHC.Types.Char
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume Data.ByteString.Lazy.Char8.scanl1
    :: (GHC.Types.Char -> GHC.Types.Char -> GHC.Types.Char)
    -> i : { i : Data.ByteString.Lazy.ByteString | 1 <= bllen i }
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume Data.ByteString.Lazy.Char8.scanr
    :: (GHC.Types.Char -> GHC.Types.Char -> GHC.Types.Char)
    -> GHC.Types.Char
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume Data.ByteString.Lazy.Char8.scanr1
    :: (GHC.Types.Char -> GHC.Types.Char -> GHC.Types.Char)
    -> i : { i : Data.ByteString.Lazy.ByteString | 1 <= bllen i }
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume Data.ByteString.Lazy.Char8.mapAccumL
    :: (acc -> GHC.Types.Char -> (acc, GHC.Types.Char))
    -> acc
    -> i : Data.ByteString.Lazy.ByteString
    -> (acc, { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i })

assume Data.ByteString.Lazy.Char8.mapAccumR
    :: (acc -> GHC.Types.Char -> (acc, GHC.Types.Char))
    -> acc
    -> i : Data.ByteString.Lazy.ByteString
    -> (acc, { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i })

assume Data.ByteString.Lazy.Char8.replicate
    :: n : Int64
    -> GHC.Types.Char
    -> { bs : Data.ByteString.Lazy.ByteString | bllen bs == n }

assume Data.ByteString.Lazy.Char8.takeWhile
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }

assume Data.ByteString.Lazy.Char8.dropWhile
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }

assume Data.ByteString.Lazy.Char8.span
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> ( { l : Data.ByteString.Lazy.ByteString | bllen l <= bllen i }
       , { r : Data.ByteString.Lazy.ByteString | bllen r <= bllen i }
       )

assume Data.ByteString.Lazy.Char8.break
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> ( { l : Data.ByteString.Lazy.ByteString | bllen l <= bllen i }
       , { r : Data.ByteString.Lazy.ByteString | bllen r <= bllen i }
       )

assume Data.ByteString.Lazy.Char8.groupBy
    :: (GHC.Types.Char -> GHC.Types.Char -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | 1 <= bllen o && bllen o <= bllen i }]

assume Data.ByteString.Lazy.Char8.split
    :: GHC.Types.Char
    -> i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }]

assume Data.ByteString.Lazy.Char8.splitWith
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }]

assume Data.ByteString.Lazy.Char8.lines
    :: i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }]

assume Data.ByteString.Lazy.Char8.words
    :: i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }]

assume Data.ByteString.Lazy.Char8.unlines
    :: is : [Data.ByteString.Lazy.ByteString]
    -> { o : Data.ByteString.Lazy.ByteString | (len is == 0 <=> bllen o == 0) && bllen o >= len is }

assume Data.ByteString.Lazy.Char8.unwords
    :: is : [Data.ByteString.Lazy.ByteString]
    -> { o : Data.ByteString.Lazy.ByteString | (len is == 0 ==> bllen o == 0) && (1 <= len is ==> bllen o >= len is - 1) }

assume Data.ByteString.Lazy.Char8.elem
    :: GHC.Types.Char
    -> bs : Data.ByteString.Lazy.ByteString
    -> { b : GHC.Types.Bool | bllen bs == 0 ==> not b }

assume Data.ByteString.Lazy.Char8.notElem
    :: GHC.Types.Char
    -> bs : Data.ByteString.Lazy.ByteString
    -> { b : GHC.Types.Bool | bllen bs == 0 ==> b }

assume Data.ByteString.Lazy.Char8.find
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> Maybe { w8 : GHC.Types.Char | bllen bs /= 0 }

assume Data.ByteString.Lazy.Char8.filter
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }

assume Data.ByteString.Lazy.Char8.index
    :: bs : Data.ByteString.Lazy.ByteString
    -> { n : Int64 | 0 <= n && n < bllen bs }
    -> GHC.Types.Char

assume Data.ByteString.Lazy.Char8.elemIndex
    :: GHC.Types.Char
    -> bs : Data.ByteString.Lazy.ByteString
    -> Maybe { n : Int64 | 0 <= n && n < bllen bs }

assume Data.ByteString.Lazy.Char8.elemIndices
    :: GHC.Types.Char
    -> bs : Data.ByteString.Lazy.ByteString
    -> [{ n : Int64 | 0 <= n && n < bllen bs }]

assume Data.ByteString.Lazy.Char8.findIndex
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> Maybe { n : Int64 | 0 <= n && n < bllen bs }

assume Data.ByteString.Lazy.Char8.findIndices
    :: (GHC.Types.Char -> GHC.Types.Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> [{ n : Int64 | 0 <= n && n < bllen bs }]

assume Data.ByteString.Lazy.Char8.count
    :: GHC.Types.Char
    -> bs : Data.ByteString.Lazy.ByteString
    -> { n : Int64 | 0 <= n && n < bllen bs }

assume Data.ByteString.Lazy.Char8.zip
    :: l : Data.ByteString.Lazy.ByteString
    -> r : Data.ByteString.Lazy.ByteString
    -> { o : [(GHC.Types.Char, GHC.Types.Char)] | len o <= bllen l && len o <= bllen r }

assume Data.ByteString.Lazy.Char8.zipWith
    :: (GHC.Types.Char -> GHC.Types.Char -> a)
    -> l : Data.ByteString.Lazy.ByteString
    -> r : Data.ByteString.Lazy.ByteString
    -> { o : [a] | len o <= bllen l && len o <= bllen r }

assume Data.ByteString.Lazy.Char8.unzip
    :: i : [(GHC.Types.Char, GHC.Types.Char)]
    -> ( { l : Data.ByteString.Lazy.ByteString | bllen l == len i }
       , { r : Data.ByteString.Lazy.ByteString | bllen r == len i }
       )

assume Data.ByteString.Lazy.ReadInt.readInt
    :: i : Data.ByteString.Lazy.ByteString
    -> Maybe { p : (Int, { o : Data.ByteString.Lazy.ByteString | bllen o < bllen i}) | bllen i /= 0 }

assume Data.ByteString.Lazy.ReadNat.readInteger
    :: i : Data.ByteString.Lazy.ByteString
    -> Maybe { p : (Integer, { o : Data.ByteString.Lazy.ByteString | bllen o < bllen i}) | bllen i /= 0 }

@-}
