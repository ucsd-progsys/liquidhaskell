module Data.ByteString.Lazy.Qualifiers (zoo) where 

-- dummy module for qualifiers required by Lazy BS.


-- ByteString qualifiers
{-@ qualif LBLensAcc(v:Data.ByteString.Lazy.Internal.ByteString,
                     bs:List Data.ByteString.Lazy.Internal.ByteString,
                     b:Data.ByteString.Lazy.Internal.ByteString):
        lbLength(v) = lbLengths(bs) + lbLength(b)
  @-}

{-@ qualif ByteStringNE(v:Data.ByteString.Internal.ByteString): (bLength v) > 0 @-}
{-@ qualif BLengthsAcc(v:List Data.ByteString.Internal.ByteString,
                       c:Data.ByteString.Internal.ByteString,
                       cs:List Data.ByteString.Internal.ByteString):
        (bLengths v) = (bLength c) + (bLengths cs)
  @-}

{-@ qualif BLengthsSum(v:List List a, bs:List Data.ByteString.Internal.ByteString):
       (sumLens v) = (bLengths bs)
  @-}

{-@ qualif BLenLE(v:Data.ByteString.Internal.ByteString, n:int): (bLength v) <= n @-}
{-@ qualif BLenEq(v:Data.ByteString.Internal.ByteString,
                  b:Data.ByteString.Internal.ByteString):
       (bLength v) = (bLength b)
  @-}

{-@ qualif BLenAcc(v:int,
                   b1:Data.ByteString.Internal.ByteString,
                   b2:Data.ByteString.Internal.ByteString):
       v = (bLength b1) + (bLength b2)
  @-}
{-@ qualif BLenAcc(v:int,
                   b:Data.ByteString.Internal.ByteString,
                   n:int):
       v = (bLength b) + n
  @-}

-- lazy ByteString qualifiers
{-@ qualif LByteStringN(v:Data.ByteString.Lazy.Internal.ByteString, n:int): (lbLength v) = n @-}
{-@ qualif LByteStringNE(v:Data.ByteString.Lazy.Internal.ByteString): (lbLength v) > 0 @-}
{-@ qualif LByteStringSZ(v:Data.ByteString.Lazy.Internal.ByteString,
                         b:Data.ByteString.Lazy.Internal.ByteString):
        (lbLength v) = (lbLength b)
  @-}

{-@ qualif LBLenAcc(v:int,
                    b1:Data.ByteString.Lazy.Internal.ByteString,
                    b2:Data.ByteString.Lazy.Internal.ByteString):
       v = (lbLength b1) + (lbLength b2)
  @-}

{-@ qualif LBLenAcc(v:int,
                    b:Data.ByteString.Lazy.Internal.ByteString,
                    n:int):
       v = (lbLength b) + n
  @-}

{-@ qualif Chunk(v:Data.ByteString.Lazy.Internal.ByteString,
                 sb:Data.ByteString.Internal.ByteString,
                 lb:Data.ByteString.Lazy.Internal.ByteString):
       (lbLength v) = (bLength sb) + (lbLength lb)
  @-}

--LIQUID for the myriad `comb` inner functions
{-@ qualif LBComb(v:List Data.ByteString.Lazy.Internal.ByteString,
                  acc:List Data.ByteString.Internal.ByteString,
                  ss:List Data.ByteString.Internal.ByteString,
                  cs:Data.ByteString.Lazy.Internal.ByteString):
        ((lbLengths v) + (len v) - 1) = ((bLengths acc) + ((bLengths ss) + (len ss) - 1) + (lbLength cs))
  @-}

{-@ qualif LBGroup(v:List Data.ByteString.Lazy.Internal.ByteString,
                   acc:List Data.ByteString.Internal.ByteString,
                   ss:List Data.ByteString.Internal.ByteString,
                   cs:Data.ByteString.Lazy.Internal.ByteString):
        (lbLengths v) = ((bLengths acc) + (bLengths ss) + (lbLength cs))
  @-}

{-@ qualif LBLenIntersperse(v:Data.ByteString.Lazy.Internal.ByteString,
                            sb:Data.ByteString.Internal.ByteString,
                            lb:Data.ByteString.Lazy.Internal.ByteString):
        (lbLength v) = ((bLength sb) * 2) + (lbLength lb)
 @-}

{-@ qualif BLenDouble(v:Data.ByteString.Internal.ByteString,
                      b:Data.ByteString.Internal.ByteString):
        (bLength v) = (bLength b) * 2
 @-}

{-@ qualif LBLenDouble(v:Data.ByteString.Lazy.Internal.ByteString,
                       b:Data.ByteString.Lazy.Internal.ByteString):
        (lbLength v) = (lbLength b) * 2
 @-}

{-@ qualif RevChunksAcc(v:Data.ByteString.Lazy.Internal.ByteString,
                        acc:Data.ByteString.Lazy.Internal.ByteString,
                        cs:List Data.ByteString.Internal.ByteString):
        (lbLength v) = (lbLength acc) + (bLengths cs)
  @-}

{-@ qualif LBSumLens(v:Data.ByteString.Lazy.Internal.ByteString,
                     z:Data.ByteString.Lazy.Internal.ByteString,
                     cs:List List a):
        (lbLength v) = (lbLength z) + (sumLens cs)
  @-}
{-@ qualif LBCountAcc(v:int,
                     c:Data.ByteString.Internal.ByteString,
                     cs:Data.ByteString.Lazy.Internal.ByteString):
       v <= (bLength c) + (lbLength cs)
  @-}



zoo :: Int -> Int
zoo = undefined
