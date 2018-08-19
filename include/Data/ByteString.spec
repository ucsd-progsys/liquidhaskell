module spec Data.ByteString where

import Data.String

measure bslen :: Data.ByteString.ByteString -> { n : Int | 0 <= n }

invariant { bs : Data.ByteString.ByteString  | 0 <= bslen bs }

invariant { bs : Data.ByteString.ByteString | bslen bs == stringlen bs }

empty :: { bs : Data.ByteString.ByteString | bslen bs == 0 }

singleton :: _ -> { bs : Data.ByteString.ByteString | bslen bs == 1 }

pack :: w8s : [_]
     -> { bs : Data.ByteString.ByteString | bslen bs == len w8s }

unpack :: bs : Data.ByteString.ByteString
       -> { w8s : [_] | len w8s == bslen bs }

cons :: _
     -> i : Data.ByteString.ByteString
     -> { o : Data.ByteString.ByteString | bslen o == bslen i + 1 }

snoc :: i : Data.ByteString.ByteString
     -> _
     -> { o : Data.ByteString.ByteString | bslen o == bslen i + 1 }

append :: l : Data.ByteString.ByteString
       -> r : Data.ByteString.ByteString
       -> { o : Data.ByteString.ByteString | bslen o == bslen l + bslen r }

head :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> _

unsnoc :: i:Data.ByteString.ByteString 
       -> (Maybe ({ o : Data.ByteString.ByteString | bslen o == bslen i - 1 }, _))

last :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> _

tail :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> _

init 
  :: {i:Data.ByteString.ByteString | 1 <= bslen i } 
  -> {o:Data.ByteString.ByteString | bslen o == bslen i - 1 }

null 
  :: bs : Data.ByteString.ByteString
  -> { b : Bool | b <=> bslen bs == 0 }

length :: bs : Data.ByteString.ByteString -> { n : Int | bslen bs == n }

map 
  :: (_ -> _)
  -> i : Data.ByteString.ByteString
  -> { o : Data.ByteString.ByteString | bslen o == bslen i }

reverse 
  :: i : Data.ByteString.ByteString
  -> { o : Data.ByteString.ByteString | bslen o == bslen i }

intersperse 
  :: _
  -> i : Data.ByteString.ByteString
  -> { o : Data.ByteString.ByteString | (bslen i == 0 <=> bslen o == 0) && (1 <= bslen i <=> bslen o == 2 * bslen i - 1) }

intercalate 
  :: l : Data.ByteString.ByteString
  -> rs : [Data.ByteString.ByteString]
  -> { o : Data.ByteString.ByteString | len rs == 0 ==> bslen o == 0 }

transpose 
  :: is : [Data.ByteString.ByteString]
  -> { os : [{ bs : Data.ByteString.ByteString | bslen bs <= len is }] | len is == 0 ==> len os == 0}

foldl1 
  :: (_ -> _ -> _)
  -> { bs : Data.ByteString.ByteString | 1 <= bslen bs }
  -> _

foldl1' 
  :: (_ -> _ -> _)
  -> { bs : Data.ByteString.ByteString | 1 <= bslen bs }
  -> _

foldr1 
  :: (_ -> _ -> _)
  -> { bs : Data.ByteString.ByteString | 1 <= bslen bs }
  -> _

foldr1' 
  :: (_ -> _ -> _)
  -> { bs : Data.ByteString.ByteString | 1 <= bslen bs }
  -> _

concat 
  :: is : [Data.ByteString.ByteString]
  -> { o : Data.ByteString.ByteString | len is == 0 ==> bslen o }

concatMap 
  :: (_ -> Data.ByteString.ByteString)
  -> i : Data.ByteString.ByteString
  -> { o : Data.ByteString.ByteString | bslen i == 0 ==> bslen o == 0 }

any 
  :: (_ -> Bool)
  -> bs : Data.ByteString.ByteString
  -> { b : Bool | bslen bs == 0 ==> not b }

all 
  :: (_ -> Bool)
  -> bs : Data.ByteString.ByteString
  -> { b : Bool | bslen bs == 0 ==> b }

maximum :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> _

minimum :: { bs : Data.ByteString.ByteString | 1 <= bslen bs } -> _

scanl :: (_ -> _ -> _)
      -> _
      -> i : Data.ByteString.ByteString
      -> { o : Data.ByteString.ByteString | bslen o == bslen i }

scanl1 :: (_ -> _ -> _)
       -> i : { i : Data.ByteString.ByteString | 1 <= bslen i }
       -> { o : Data.ByteString.ByteString | bslen o == bslen i }

scanr
    :: (_ -> _ -> _)
    -> _
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

scanr1
    :: (_ -> _ -> _)
    -> i : { i : Data.ByteString.ByteString | 1 <= bslen i }
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

mapAccumL
    :: (acc -> _ -> (acc, _))
    -> acc
    -> i : Data.ByteString.ByteString
    -> (acc, { o : Data.ByteString.ByteString | bslen o == bslen i })

mapAccumR
    :: (acc -> _ -> (acc, _))
    -> acc
    -> i : Data.ByteString.ByteString
    -> (acc, { o : Data.ByteString.ByteString | bslen o == bslen i })

replicate
    :: n : Int
    -> _
    -> { bs : Data.ByteString.ByteString | bslen bs == n }

unfoldrN
    :: n : Int
    -> (a -> Maybe (_, a))
    -> a
    -> ({ bs : Data.ByteString.ByteString | bslen bs <= n }, Maybe a)

take
    :: n : Int
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | (n <= 0 <=> bslen o == 0) &&
                                          ((0 <= n && n <= bslen i) <=> bslen o == n) &&
                                          (bslen i <= n <=> bslen o = bslen i) }

drop
    :: n : Int
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | (n <= 0 <=> bslen o == bslen i) &&
                                          ((0 <= n && n <= bslen i) <=> bslen o == bslen i - n) &&
                                          (bslen i <= n <=> bslen o == 0) }

splitAt
    :: n : Int
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | (n <= 0 <=> bslen l == 0) &&
                                            ((0 <= n && n <= bslen i) <=> bslen l == n) &&
                                            (bslen i <= n <=> bslen l == bslen i) }
       , { r : Data.ByteString.ByteString | (n <= 0 <=> bslen r == bslen i) &&
                                            ((0 <= n && n <= bslen i) <=> bslen r == bslen i - n) &&
                                            (bslen i <= n <=> bslen r == 0) }
       )

takeWhile
    :: (_ -> Bool)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o <= bslen i }

dropWhile
    :: (_ -> Bool)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o <= bslen i }

span
    :: (_ -> Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

spanEnd
    :: (_ -> Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

break
    :: (_ -> Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

breakEnd
    :: (_ -> Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

group
    :: i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | 1 <= bslen o && bslen o <= bslen i }]

groupBy
    :: (_ -> _ -> Bool)
    -> i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | 1 <= bslen o && bslen o <= bslen i }]

inits
    :: i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | bslen o <= bslen i }]

tails
    :: i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | bslen o <= bslen i }]

split
    :: _
    -> i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | bslen o <= bslen i }]

splitWith
    :: (_ -> Bool)
    -> i : Data.ByteString.ByteString
    -> [{ o : Data.ByteString.ByteString | bslen o <= bslen i }]

isPrefixOf
    :: l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { b : Bool | bslen l >= bslen r ==> not b }

isSuffixOf
    :: l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { b : Bool | bslen l > bslen r ==> not b }

isInfixOf
    :: l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { b : Bool | bslen l > bslen r ==> not b }

breakSubstring
    :: il : Data.ByteString.ByteString
    -> ir : Data.ByteString.ByteString
    -> ( { ol : Data.ByteString.ByteString | bslen ol <= bslen ir && (bslen il > bslen ir ==> bslen ol == bslen ir)}
       , { or : Data.ByteString.ByteString | bslen or <= bslen ir && (bslen il > bslen ir ==> bslen or == 0) }
       )

elem
    :: _
    -> bs : Data.ByteString.ByteString
    -> { b : Bool | bslen b == 0 ==> not b }

notElem
    :: _
    -> bs : Data.ByteString.ByteString
    -> { b : Bool | bslen b == 0 ==> b }

find
    :: (_ -> Bool)
    -> bs : Data.ByteString.ByteString
    -> (Maybe { w8 : _ | bslen bs /= 0 })

filter
    :: (_ -> Bool)
    -> i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o <= bslen i }

partition
    :: (_ -> Bool)
    -> i : Data.ByteString.ByteString
    -> ( { l : Data.ByteString.ByteString | bslen l <= bslen i }
       , { r : Data.ByteString.ByteString | bslen r <= bslen i }
       )

index :: bs : Data.ByteString.ByteString -> { n : Int | 0 <= n && n < bslen bs } -> _

elemIndex
    :: _
    -> bs : Data.ByteString.ByteString
    -> (Maybe { n : Int | 0 <= n && n < bslen bs })

elemIndices
    :: _
    -> bs : Data.ByteString.ByteString
    -> [{ n : Int | 0 <= n && n < bslen bs }]

elemIndexEnd
    :: _
    -> bs : Data.ByteString.ByteString
    -> (Maybe { n : Int | 0 <= n && n < bslen bs })

findIndex
    :: (_ -> Bool)
    -> bs : Data.ByteString.ByteString
    -> (Maybe { n : Int | 0 <= n && n < bslen bs })

findIndices
    :: (_ -> Bool)
    -> bs : Data.ByteString.ByteString
    -> [{ n : Int | 0 <= n && n < bslen bs }]

count
    :: _
    -> bs : Data.ByteString.ByteString
    -> { n : Int | 0 <= n && n < bslen bs }

zip
    :: l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { o : [(_, _)] | len o <= bslen l && len o <= bslen r }

zipWith
    :: (_ -> _ -> a)
    -> l : Data.ByteString.ByteString
    -> r : Data.ByteString.ByteString
    -> { o : [a] | len o <= bslen l && len o <= bslen r }

unzip
    :: i : [(_, _)]
    -> ( { l : Data.ByteString.ByteString | bslen l == len i }
       , { r : Data.ByteString.ByteString | bslen r == len i }
       )

sort
    :: i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

copy
    :: i : Data.ByteString.ByteString
    -> { o : Data.ByteString.ByteString | bslen o == bslen i }

hGet
    :: _
    -> n : { n : Int | 0 <= n }
    -> (IO { bs : Data.ByteString.ByteString | bslen bs == n || bslen bs == 0 })

hGetSome
    :: _
    -> n : { n : Int | 0 <= n }
    -> (IO { bs : Data.ByteString.ByteString | bslen bs <= n })

hGetNonBlocking
    :: _
    -> n : { n : Int | 0 <= n }
    -> (IO { bs : Data.ByteString.ByteString | bslen bs <= n })

uncons
    :: i : Data.ByteString.ByteString
    -> (Maybe (_, { o : Data.ByteString.ByteString | bslen o == bslen i - 1 }))
    