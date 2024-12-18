{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Data.ByteString.Lazy.Char8_LHAssumptions where

import Data.ByteString.Lazy hiding (hGetNonBlocking, scanl)
import Data.ByteString.Lazy.Char8
import Data.ByteString.Lazy_LHAssumptions()
import Data.Int

{-@
assume Data.ByteString.Lazy.Char8.last :: { bs : ByteString | 1 <= bllen bs } -> Char

assume Data.ByteString.Lazy.Char8.singleton
    :: Char -> { bs : ByteString | bllen bs == 1 }

assume Data.ByteString.Lazy.Char8.pack
    :: w8s : [Char]
    -> { bs : ByteString | bllen bs == len w8s }

assume Data.ByteString.Lazy.Char8.unpack
    :: bs : ByteString
    -> { w8s : [Char] | len w8s == bllen bs }

assume Data.ByteString.Lazy.Char8.cons
    :: Char
    -> i : ByteString
    -> { o : ByteString | bllen o == bllen i + 1 }

assume Data.ByteString.Lazy.Char8.snoc
    :: i : ByteString
    -> Char
    -> { o : ByteString | bllen o == bllen i + 1 }

assume Data.ByteString.Lazy.Char8.head
    :: { bs : ByteString | 1 <= bllen bs }
    -> Char

assume Data.ByteString.Lazy.Char8.uncons
    :: i : ByteString
    -> Maybe (Char, { o : ByteString | bllen o == bllen i - 1 })

assume Data.ByteString.Lazy.Char8.unsnoc
    :: i : ByteString
    -> Maybe ({ o : ByteString | bllen o == bllen i - 1 }, Char)

assume Data.ByteString.Lazy.Char8.map
    :: (Char -> Char)
    -> i : ByteString
    -> { o : ByteString | bllen o == bllen i }

assume Data.ByteString.Lazy.Char8.intersperse
    :: Char
    -> i : ByteString
    -> { o : ByteString | (bllen i == 0 <=> bllen o == 0) && (1 <= bllen i <=> bllen o == 2 * bllen i - 1) }

assume Data.ByteString.Lazy.Char8.foldl1
    :: (Char -> Char -> Char)
    -> { bs : ByteString | 1 <= bllen bs }
    -> Char

assume Data.ByteString.Lazy.Char8.foldl1'
    :: (Char -> Char -> Char)
    -> { bs : ByteString | 1 <= bllen bs }
    -> Char

assume Data.ByteString.Lazy.Char8.foldr1
    :: (Char -> Char -> Char)
    -> { bs : ByteString | 1 <= bllen bs }
    -> Char

assume Data.ByteString.Lazy.Char8.concatMap
    :: (Char -> ByteString)
    -> i : ByteString
    -> { o : ByteString | bllen i == 0 ==> bllen o == 0 }

assume Data.ByteString.Lazy.Char8.any :: (Char -> Bool)
    -> bs : ByteString
    -> { b : Bool | bllen bs == 0 ==> not b }

assume Data.ByteString.Lazy.Char8.all :: (Char -> Bool)
    -> bs : ByteString
    -> { b : Bool | bllen bs == 0 ==> b }

assume Data.ByteString.Lazy.Char8.maximum :: { bs : ByteString | 1 <= bllen bs } -> Char

assume Data.ByteString.Lazy.Char8.minimum :: { bs : ByteString | 1 <= bllen bs } -> Char

assume Data.ByteString.Lazy.Char8.scanl
    :: (Char -> Char -> Char)
    -> Char
    -> i : ByteString
    -> { o : ByteString | bllen o == bllen i }

assume Data.ByteString.Lazy.Char8.scanl1
    :: (Char -> Char -> Char)
    -> i : { i : ByteString | 1 <= bllen i }
    -> { o : ByteString | bllen o == bllen i }

assume Data.ByteString.Lazy.Char8.scanr
    :: (Char -> Char -> Char)
    -> Char
    -> i : ByteString
    -> { o : ByteString | bllen o == bllen i }

assume Data.ByteString.Lazy.Char8.scanr1
    :: (Char -> Char -> Char)
    -> i : { i : ByteString | 1 <= bllen i }
    -> { o : ByteString | bllen o == bllen i }

assume Data.ByteString.Lazy.Char8.mapAccumL
    :: (acc -> Char -> (acc, Char))
    -> acc
    -> i : ByteString
    -> (acc, { o : ByteString | bllen o == bllen i })

assume Data.ByteString.Lazy.Char8.mapAccumR
    :: (acc -> Char -> (acc, Char))
    -> acc
    -> i : ByteString
    -> (acc, { o : ByteString | bllen o == bllen i })

assume Data.ByteString.Lazy.Char8.replicate
    :: n : Int64
    -> Char
    -> { bs : ByteString | bllen bs == n }

assume Data.ByteString.Lazy.Char8.takeWhile
    :: (Char -> Bool)
    -> i : ByteString
    -> { o : ByteString | bllen o <= bllen i }

assume Data.ByteString.Lazy.Char8.dropWhile
    :: (Char -> Bool)
    -> i : ByteString
    -> { o : ByteString | bllen o <= bllen i }

assume Data.ByteString.Lazy.Char8.span
    :: (Char -> Bool)
    -> i : ByteString
    -> ( { l : ByteString | bllen l <= bllen i }
       , { r : ByteString | bllen r <= bllen i }
       )

assume Data.ByteString.Lazy.Char8.break
    :: (Char -> Bool)
    -> i : ByteString
    -> ( { l : ByteString | bllen l <= bllen i }
       , { r : ByteString | bllen r <= bllen i }
       )

assume Data.ByteString.Lazy.Char8.groupBy
    :: (Char -> Char -> Bool)
    -> i : ByteString
    -> [{ o : ByteString | 1 <= bllen o && bllen o <= bllen i }]

assume Data.ByteString.Lazy.Char8.split
    :: Char
    -> i : ByteString
    -> [{ o : ByteString | bllen o <= bllen i }]

assume Data.ByteString.Lazy.Char8.splitWith
    :: (Char -> Bool)
    -> i : ByteString
    -> [{ o : ByteString | bllen o <= bllen i }]

assume Data.ByteString.Lazy.Char8.lines
    :: i : ByteString
    -> [{ o : ByteString | bllen o <= bllen i }]

assume Data.ByteString.Lazy.Char8.words
    :: i : ByteString
    -> [{ o : ByteString | bllen o <= bllen i }]

assume Data.ByteString.Lazy.Char8.unlines
    :: is : [ByteString]
    -> { o : ByteString | (len is == 0 <=> bllen o == 0) && bllen o >= len is }

assume Data.ByteString.Lazy.Char8.unwords
    :: is : [ByteString]
    -> { o : ByteString | (len is == 0 ==> bllen o == 0) && (1 <= len is ==> bllen o >= len is - 1) }

assume Data.ByteString.Lazy.Char8.elem
    :: Char
    -> bs : ByteString
    -> { b : Bool | bllen bs == 0 ==> not b }

assume Data.ByteString.Lazy.Char8.notElem
    :: Char
    -> bs : ByteString
    -> { b : Bool | bllen bs == 0 ==> b }

assume Data.ByteString.Lazy.Char8.find
    :: (Char -> Bool)
    -> bs : ByteString
    -> Maybe { w8 : Char | bllen bs /= 0 }

assume Data.ByteString.Lazy.Char8.filter
    :: (Char -> Bool)
    -> i : ByteString
    -> { o : ByteString | bllen o <= bllen i }

assume Data.ByteString.Lazy.Char8.index
    :: bs : ByteString
    -> { n : Int64 | 0 <= n && n < bllen bs }
    -> Char

assume Data.ByteString.Lazy.Char8.elemIndex
    :: Char
    -> bs : ByteString
    -> Maybe { n : Int64 | 0 <= n && n < bllen bs }

assume Data.ByteString.Lazy.Char8.elemIndices
    :: Char
    -> bs : ByteString
    -> [{ n : Int64 | 0 <= n && n < bllen bs }]

assume Data.ByteString.Lazy.Char8.findIndex
    :: (Char -> Bool)
    -> bs : ByteString
    -> Maybe { n : Int64 | 0 <= n && n < bllen bs }

assume Data.ByteString.Lazy.Char8.findIndices
    :: (Char -> Bool)
    -> bs : ByteString
    -> [{ n : Int64 | 0 <= n && n < bllen bs }]

assume Data.ByteString.Lazy.Char8.count
    :: Char
    -> bs : ByteString
    -> { n : Int64 | 0 <= n && n < bllen bs }

assume Data.ByteString.Lazy.Char8.zip
    :: l : ByteString
    -> r : ByteString
    -> { o : [(Char, Char)] | len o <= bllen l && len o <= bllen r }

assume Data.ByteString.Lazy.Char8.zipWith
    :: (Char -> Char -> a)
    -> l : ByteString
    -> r : ByteString
    -> { o : [a] | len o <= bllen l && len o <= bllen r }

assume Data.ByteString.Lazy.Char8.unzip
    :: i : [(Char, Char)]
    -> ( { l : ByteString | bllen l == len i }
       , { r : ByteString | bllen r == len i }
       )

assume readInt
    :: i : ByteString
    -> Maybe { p : (Int, { o : ByteString | bllen o < bllen i}) | bllen i /= 0 }

assume readInteger
    :: i : ByteString
    -> Maybe { p : (Integer, { o : ByteString | bllen o < bllen i}) | bllen i /= 0 }

@-}
