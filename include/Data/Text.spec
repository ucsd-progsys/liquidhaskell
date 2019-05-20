module spec Data.Text where

import Data.String

measure tlen :: Data.Text.Text -> { n : Int | 0 <= n }

invariant { t : Data.Text.Text  | 0 <= tlen t }

invariant { t : Data.Text.Text | tlen t == stringlen t }

empty :: { t : Data.Text.Text | tlen t == 0 }

singleton :: _ -> { t : Data.Text.Text | tlen t == 1 }

pack :: str : [_]
     -> { t : Data.Text.Text | tlen t == len str }

unpack :: t : Data.Text.Text
       -> { str : [_] | len str == tlen t }

cons :: _
     -> i : Data.Text.Text
     -> { o : Data.Text.Text | tlen o == tlen i + 1 }

snoc :: i : Data.Text.Text
     -> _
     -> { o : Data.Text.Text | tlen o == tlen i + 1 }

append :: l : Data.Text.Text
       -> r : Data.Text.Text
       -> { o : Data.Text.Text | tlen o == tlen l + tlen r }

head :: { t : Data.Text.Text | 1 <= tlen t } -> _

unsnoc :: i:Data.Text.Text
       -> (Maybe ({ o : Data.Text.Text | tlen o == tlen i - 1 }, _))

last :: { t : Data.Text.Text | 1 <= tlen t } -> _

tail :: { t : Data.Text.Text | 1 <= tlen t } -> _

init
  :: {i:Data.Text.Text | 1 <= tlen i }
  -> {o:Data.Text.Text | tlen o == tlen i - 1 }

null
  :: t : Data.Text.Text
  -> { b : GHC.Types.Bool | b <=> tlen t == 0 }

length :: t : Data.Text.Text -> { n : Int | tlen t == n }

map
  :: (_ -> _)
  -> i : Data.Text.Text
  -> { o : Data.Text.Text | tlen o == tlen i }

reverse
  :: i : Data.Text.Text
  -> { o : Data.Text.Text | tlen o == tlen i }

intersperse
  :: _
  -> i : Data.Text.Text
  -> { o : Data.Text.Text | (tlen i == 0 <=> tlen o == 0) && (1 <= tlen i <=> tlen o == 2 * tlen i - 1) }

intercalate
  :: l : Data.Text.Text
  -> rs : [Data.Text.Text]
  -> { o : Data.Text.Text | len rs == 0 ==> tlen o == 0 }

transpose
  :: is : [Data.Text.Text]
  -> { os : [{ t : Data.Text.Text | tlen t <= len is }] | len is == 0 ==> len os == 0}

foldl1
  :: (_ -> _ -> _)
  -> { t : Data.Text.Text | 1 <= tlen t }
  -> _

foldl1'
  :: (_ -> _ -> _)
  -> { t : Data.Text.Text | 1 <= tlen t }
  -> _

foldr1
  :: (_ -> _ -> _)
  -> { t : Data.Text.Text | 1 <= tlen t }
  -> _

concat
  :: is : [Data.Text.Text]
  -> { o : Data.Text.Text | (len is == 0) ==> (tlen o == 0) }

concatMap
  :: (_ -> Data.Text.Text)
  -> i : Data.Text.Text
  -> { o : Data.Text.Text | tlen i == 0 ==> tlen o == 0 }

any
  :: (_ -> GHC.Types.Bool)
  -> t : Data.Text.Text
  -> { b : GHC.Types.Bool | tlen t == 0 ==> not b }

all
  :: (_ -> GHC.Types.Bool)
  -> t : Data.Text.Text
  -> { b : GHC.Types.Bool | tlen t == 0 ==> b }

maximum :: { t : Data.Text.Text | 1 <= tlen t } -> _

minimum :: { t : Data.Text.Text | 1 <= tlen t } -> _

scanl :: (_ -> _ -> _)
      -> _
      -> i : Data.Text.Text
      -> { o : Data.Text.Text | tlen o == tlen i }

scanl1 :: (_ -> _ -> _)
       -> i : { i : Data.Text.Text | 1 <= tlen i }
       -> { o : Data.Text.Text | tlen o == tlen i }

scanr
    :: (_ -> _ -> _)
    -> _
    -> i : Data.Text.Text
    -> { o : Data.Text.Text | tlen o == tlen i }

scanr1
    :: (_ -> _ -> _)
    -> i : { i : Data.Text.Text | 1 <= tlen i }
    -> { o : Data.Text.Text | tlen o == tlen i }

mapAccumL
    :: (acc -> _ -> (acc, _))
    -> acc
    -> i : Data.Text.Text
    -> (acc, { o : Data.Text.Text | tlen o == tlen i })

mapAccumR
    :: (acc -> _ -> (acc, _))
    -> acc
    -> i : Data.Text.Text
    -> (acc, { o : Data.Text.Text | tlen o == tlen i })

replicate
    :: n : Int
    -> _
    -> { t : Data.Text.Text | tlen t == n }

unfoldrN
    :: n : Int
    -> (a -> Maybe (_, a))
    -> a
    -> { t : Data.Text.Text | tlen t <= n }

take
    :: n : Int
    -> i : Data.Text.Text
    -> { o : Data.Text.Text | (n <= 0 <=> tlen o == 0) &&
                                          ((0 <= n && n <= tlen i) <=> tlen o == n) &&
                                          (tlen i <= n <=> tlen o = tlen i) }

drop
    :: n : Int
    -> i : Data.Text.Text
    -> { o : Data.Text.Text | (n <= 0 <=> tlen o == tlen i) &&
                                          ((0 <= n && n <= tlen i) <=> tlen o == tlen i - n) &&
                                          (tlen i <= n <=> tlen o == 0) }

splitAt
    :: n : Int
    -> i : Data.Text.Text
    -> ( { l : Data.Text.Text | (n <= 0 <=> tlen l == 0) &&
                                            ((0 <= n && n <= tlen i) <=> tlen l == n) &&
                                            (tlen i <= n <=> tlen l == tlen i) }
       , { r : Data.Text.Text | (n <= 0 <=> tlen r == tlen i) &&
                                            ((0 <= n && n <= tlen i) <=> tlen r == tlen i - n) &&
                                            (tlen i <= n <=> tlen r == 0) }
       )

takeWhile
    :: (_ -> GHC.Types.Bool)
    -> i : Data.Text.Text
    -> { o : Data.Text.Text | tlen o <= tlen i }

dropWhile
    :: (_ -> GHC.Types.Bool)
    -> i : Data.Text.Text
    -> { o : Data.Text.Text | tlen o <= tlen i }

span
    :: (_ -> GHC.Types.Bool)
    -> i : Data.Text.Text
    -> ( { l : Data.Text.Text | tlen l <= tlen i }
       , { r : Data.Text.Text | tlen r <= tlen i }
       )

break
    :: (_ -> GHC.Types.Bool)
    -> i : Data.Text.Text
    -> ( { l : Data.Text.Text | tlen l <= tlen i }
       , { r : Data.Text.Text | tlen r <= tlen i }
       )

group
    :: i : Data.Text.Text
    -> [{ o : Data.Text.Text | 1 <= tlen o && tlen o <= tlen i }]

groupBy
    :: (_ -> _ -> GHC.Types.Bool)
    -> i : Data.Text.Text
    -> [{ o : Data.Text.Text | 1 <= tlen o && tlen o <= tlen i }]

inits
    :: i : Data.Text.Text
    -> [{ o : Data.Text.Text | tlen o <= tlen i }]

tails
    :: i : Data.Text.Text
    -> [{ o : Data.Text.Text | tlen o <= tlen i }]

split
    :: (_ -> GHC.Types.Bool)
    -> i : Data.Text.Text
    -> [{ o : Data.Text.Text | tlen o <= tlen i }]

isPrefixOf
    :: l : Data.Text.Text
    -> r : Data.Text.Text
    -> { b : GHC.Types.Bool | tlen l >= tlen r ==> not b }

isSuffixOf
    :: l : Data.Text.Text
    -> r : Data.Text.Text
    -> { b : GHC.Types.Bool | tlen l > tlen r ==> not b }

isInfixOf
    :: l : Data.Text.Text
    -> r : Data.Text.Text
    -> { b : GHC.Types.Bool | tlen l > tlen r ==> not b }

find
    :: (_ -> GHC.Types.Bool)
    -> t : Data.Text.Text
    -> (Maybe { char : _ | tlen t /= 0 })

filter
    :: (_ -> GHC.Types.Bool)
    -> i : Data.Text.Text
    -> { o : Data.Text.Text | tlen o <= tlen i }

partition
    :: (_ -> GHC.Types.Bool)
    -> i : Data.Text.Text
    -> ( { l : Data.Text.Text | tlen l <= tlen i }
       , { r : Data.Text.Text | tlen r <= tlen i }
       )

index :: t : Data.Text.Text -> { n : Int | 0 <= n && n < tlen t } -> _

findIndex
    :: (_ -> GHC.Types.Bool)
    -> t : Data.Text.Text
    -> (Maybe { n : Int | 0 <= n && n < tlen t })

count
    :: _
    -> t : Data.Text.Text
    -> { n : Int | 0 <= n && n < tlen t }

zip
    :: l : Data.Text.Text
    -> r : Data.Text.Text
    -> { o : [(_, _)] | len o <= tlen l && len o <= tlen r }

zipWith
    :: (_ -> _ -> Char)
    -> l : Data.Text.Text
    -> r : Data.Text.Text
    -> { o : Text | tlen o <= tlen l && tlen o <= tlen r }

copy
    :: i : Data.Text.Text
    -> { o : Data.Text.Text | tlen o == tlen i }

uncons
    :: i : Data.Text.Text
    -> (Maybe (_, { o : Data.Text.Text | tlen o == tlen i - 1 }))

