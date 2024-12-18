{-

Without the 
  define GHC.Internal.Num.fromInteger x = (x)
  define GHC.Num.Integer.IS             = (x)

this program crashes with: 

    Illegal type specification for `NumRefl.toNum`
    NumRefl.toNum :: forall p .
                     (Num<[]> p) =>
                     lq1:() -> {VV : p | VV == NumRefl.toNum lq1
                                         && VV == (-GHC.Internal.Num.fromInteger (GHC.Num.Integer.IS 1))}
    Sort Error in Refinement: {VV : p##aMJ | VV == NumRefl.toNum lq1
                                             && VV == (-GHC.Internal.Num.fromInteger (GHC.Num.Integer.IS 1))}
    The sort @(176) is not numeric

Because the resule type (Num p) => p cannot be decided to be a numeric type.
-}

module NumRefl where

{-@ reflect toNum @-}
toNum :: Num p => () -> p
toNum _ = -1


