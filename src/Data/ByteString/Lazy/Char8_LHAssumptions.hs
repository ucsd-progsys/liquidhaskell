{-# OPTIONS_GHC -Wno-unused-imports #-}
module Data.ByteString.Lazy.Char8_LHAssumptions where

import Data.ByteString.Lazy hiding (hGetNonBlocking, scanl)
import Data.ByteString.Lazy.Char8
import Data.ByteString.Lazy_LHAssumptions()

{-@
assume Data.ByteString.Lazy.Char8.last :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs } -> Char

assume Data.ByteString.Lazy.Char8.singleton
    :: Char -> { bs : Data.ByteString.Lazy.ByteString | bllen bs == 1 }

assume Data.ByteString.Lazy.Char8.pack
    :: w8s : [Char]
    -> { bs : Data.ByteString.ByteString | bllen bs == len w8s }

assume Data.ByteString.Lazy.Char8.unpack
    :: bs : Data.ByteString.Lazy.ByteString
    -> { w8s : [Char] | len w8s == bllen bs }

assume Data.ByteString.Lazy.Char8.cons
    :: Char
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i + 1 }

assume Data.ByteString.Lazy.Char8.snoc
    :: i : Data.ByteString.Lazy.ByteString
    -> Char
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i + 1 }

assume Data.ByteString.Lazy.Char8.head
    :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> Char

assume Data.ByteString.Lazy.Char8.uncons
    :: i : Data.ByteString.Lazy.ByteString
    -> Maybe (Char, { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i - 1 })

assume Data.ByteString.Lazy.Char8.unsnoc
    :: i : Data.ByteString.Lazy.ByteString
    -> Maybe ({ o : Data.ByteString.Lazy.ByteString | bllen o == bllen i - 1 }, Char)

assume Data.ByteString.Lazy.Char8.map
    :: (Char -> Char)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume Data.ByteString.Lazy.Char8.intersperse
    :: Char
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | (bllen i == 0 <=> bllen o == 0) && (1 <= bllen i <=> bllen o == 2 * bllen i - 1) }

assume Data.ByteString.Lazy.Char8.foldl1
    :: (Char -> Char -> Char)
    -> { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> Char

assume Data.ByteString.Lazy.Char8.foldl1'
    :: (Char -> Char -> Char)
    -> { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> Char

assume Data.ByteString.Lazy.Char8.foldr1
    :: (Char -> Char -> Char)
    -> { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs }
    -> Char

assume Data.ByteString.Lazy.Char8.concatMap
    :: (Char -> Data.ByteString.Lazy.ByteString)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen i == 0 ==> bllen o == 0 }

assume Data.ByteString.Lazy.Char8.any :: (Char -> GHC.Types.Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> { b : GHC.Types.Bool | bllen bs == 0 ==> not b }

assume Data.ByteString.Lazy.Char8.all :: (Char -> GHC.Types.Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> { b : GHC.Types.Bool | bllen bs == 0 ==> b }

assume Data.ByteString.Lazy.Char8.maximum :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs } -> Char

assume Data.ByteString.Lazy.Char8.minimum :: { bs : Data.ByteString.Lazy.ByteString | 1 <= bllen bs } -> Char

assume Data.ByteString.Lazy.Char8.scanl
    :: (Char -> Char -> Char)
    -> Char
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume Data.ByteString.Lazy.Char8.scanl1
    :: (Char -> Char -> Char)
    -> i : { i : Data.ByteString.Lazy.ByteString | 1 <= bllen i }
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume Data.ByteString.Lazy.Char8.scanr
    :: (Char -> Char -> Char)
    -> Char
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume Data.ByteString.Lazy.Char8.scanr1
    :: (Char -> Char -> Char)
    -> i : { i : Data.ByteString.Lazy.ByteString | 1 <= bllen i }
    -> { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i }

assume Data.ByteString.Lazy.Char8.mapAccumL
    :: (acc -> Char -> (acc, Char))
    -> acc
    -> i : Data.ByteString.Lazy.ByteString
    -> (acc, { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i })

assume Data.ByteString.Lazy.Char8.mapAccumR
    :: (acc -> Char -> (acc, Char))
    -> acc
    -> i : Data.ByteString.Lazy.ByteString
    -> (acc, { o : Data.ByteString.Lazy.ByteString | bllen o == bllen i })

assume Data.ByteString.Lazy.Char8.replicate
    :: n : Int64
    -> Char
    -> { bs : Data.ByteString.Lazy.ByteString | bllen bs == n }

assume Data.ByteString.Lazy.Char8.takeWhile
    :: (Char -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }

assume Data.ByteString.Lazy.Char8.dropWhile
    :: (Char -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }

assume Data.ByteString.Lazy.Char8.span
    :: (Char -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> ( { l : Data.ByteString.Lazy.ByteString | bllen l <= bllen i }
       , { r : Data.ByteString.Lazy.ByteString | bllen r <= bllen i }
       )

assume Data.ByteString.Lazy.Char8.break
    :: (Char -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> ( { l : Data.ByteString.Lazy.ByteString | bllen l <= bllen i }
       , { r : Data.ByteString.Lazy.ByteString | bllen r <= bllen i }
       )

assume Data.ByteString.Lazy.Char8.groupBy
    :: (Char -> Char -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | 1 <= bllen o && bllen o <= bllen i }]

assume Data.ByteString.Lazy.Char8.split
    :: Char
    -> i : Data.ByteString.Lazy.ByteString
    -> [{ o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }]

assume Data.ByteString.Lazy.Char8.splitWith
    :: (Char -> GHC.Types.Bool)
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
    :: Char
    -> bs : Data.ByteString.Lazy.ByteString
    -> { b : GHC.Types.Bool | bllen b == 0 ==> not b }

assume Data.ByteString.Lazy.Char8.notElem
    :: Char
    -> bs : Data.ByteString.Lazy.ByteString
    -> { b : GHC.Types.Bool | bllen b == 0 ==> b }

assume Data.ByteString.Lazy.Char8.find
    :: (Char -> GHC.Types.Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> Maybe { w8 : Char | bllen bs /= 0 }

assume Data.ByteString.Lazy.Char8.filter
    :: (Char -> GHC.Types.Bool)
    -> i : Data.ByteString.Lazy.ByteString
    -> { o : Data.ByteString.Lazy.ByteString | bllen o <= bllen i }

assume Data.ByteString.Lazy.Char8.index
    :: bs : Data.ByteString.Lazy.ByteString
    -> { n : Int64 | 0 <= n && n < bllen bs }
    -> Char

assume Data.ByteString.Lazy.Char8.elemIndex
    :: Char
    -> bs : Data.ByteString.Lazy.ByteString
    -> Maybe { n : Int64 | 0 <= n && n < bllen bs }

assume Data.ByteString.Lazy.Char8.elemIndices
    :: Char
    -> bs : Data.ByteString.Lazy.ByteString
    -> [{ n : Int64 | 0 <= n && n < bllen bs }]

assume Data.ByteString.Lazy.Char8.findIndex
    :: (Char -> GHC.Types.Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> Maybe { n : Int64 | 0 <= n && n < bllen bs }

assume Data.ByteString.Lazy.Char8.findIndices
    :: (Char -> GHC.Types.Bool)
    -> bs : Data.ByteString.Lazy.ByteString
    -> [{ n : Int64 | 0 <= n && n < bllen bs }]

assume Data.ByteString.Lazy.Char8.count
    :: Char
    -> bs : Data.ByteString.Lazy.ByteString
    -> { n : Int64 | 0 <= n && n < bllen bs }

assume Data.ByteString.Lazy.Char8.zip
    :: l : Data.ByteString.Lazy.ByteString
    -> r : Data.ByteString.Lazy.ByteString
    -> { o : [(Char, Char)] | len o <= bllen l && len o <= bllen r }

assume Data.ByteString.Lazy.Char8.zipWith
    :: (Char -> Char -> a)
    -> l : Data.ByteString.Lazy.ByteString
    -> r : Data.ByteString.Lazy.ByteString
    -> { o : [a] | len o <= bllen l && len o <= bllen r }

assume Data.ByteString.Lazy.Char8.unzip
    :: i : [(Char, Char)]
    -> ( { l : Data.ByteString.Lazy.ByteString | bllen l == len i }
       , { r : Data.ByteString.Lazy.ByteString | bllen r == len i }
       )

assume Data.ByteString.Lazy.Char8.readInt
    :: i : Data.ByteString.Lazy.ByteString
    -> Maybe { p : (Int, { o : Data.ByteString.Lazy.ByteString | bllen o < bllen i}) | bllen i /= 0 }

assume Data.ByteString.Lazy.Char8.readInteger
    :: i : Data.ByteString.Lazy.ByteString
    -> Maybe { p : (Integer, { o : Data.ByteString.Lazy.ByteString | bllen o < bllen i}) | bllen i /= 0 }

@-}
