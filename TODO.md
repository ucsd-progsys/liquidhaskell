# TODO

## PLE-DEBUG

GOOD [OLD]

stack exec -- fixpoint tests/todo/IndPalindrome.hs.bfq --allowho --eliminate=some --rewrite > log.old 2>&1


Trace: [INSTANTIATE i = 26] : ((isJust GHC.Base.Nothing <=> false))
&& ((((((is$GHC.Types.: GHC.Types.[] <=> false)
        && (is$GHC.Types.[] GHC.Types.[] <=> true))
       && (is$GHC.Types.: GHC.Types.[] <=> false))
      && (is$GHC.Types.[] GHC.Types.[] <=> true))
     && len GHC.Types.[] == 0))
&& (((((is$IndPalindrome.Pals IndPalindrome.Pal0 <=> false)
       && (is$IndPalindrome.Pal1 IndPalindrome.Pal0 <=> false))
      && (is$IndPalindrome.Pal0 IndPalindrome.Pal0 <=> true))
     && prop IndPalindrome.Pal0 == IndPalindrome.Pal GHC.Types.[]))
     
&& IndPalindrome.Pal (IndPalindrome.single d2DX) == IndPalindrome.Pal (GHC.Types.: d2DX GHC.Types.[])
&& len (GHC.Types.: d2DX GHC.Types.[]) == 1 + len GHC.Types.[]
&& is$GHC.Types.[] (GHC.Types.: d2DX GHC.Types.[]) == false
&& is$GHC.Types.: (GHC.Types.: d2DX GHC.Types.[]) == true
&& lqdc##$select##GHC.Types.:##1 (GHC.Types.: d2DX GHC.Types.[]) == d2DX
&& lqdc##$select##GHC.Types.:##2 (GHC.Types.: d2DX GHC.Types.[]) == GHC.Types.[]
&& is$GHC.Types.[] (GHC.Types.: d2DX GHC.Types.[]) == false
&& is$GHC.Types.: (GHC.Types.: d2DX GHC.Types.[]) == true
&& lqdc##$select##GHC.Types.:##1 (GHC.Types.: d2DX GHC.Types.[]) == d2DX
&& lqdc##$select##GHC.Types.:##2 (GHC.Types.: d2DX GHC.Types.[]) == GHC.Types.[]
&& head (GHC.Types.: d2DX GHC.Types.[]) == d2DX
&& tail (GHC.Types.: d2DX GHC.Types.[]) == GHC.Types.[]


BAD [NEW]

stack exec -- fixpoint tests/todo/IndPalindrome.hs.bfq --allowho --eliminate=some --rewrite --incr > log.new 2>&1

INCR-INSTANTIATE i = 26: 
(IndPalindrome.Pal (IndPalindrome.single d2DX) == IndPalindrome.Pal (GHC.Types.: d2DX GHC.Types.[])
 && len (GHC.Types.: d2DX GHC.Types.[]) == 1 + len GHC.Types.[]
 && is$GHC.Types.[] (GHC.Types.: d2DX GHC.Types.[]) == false
 && is$GHC.Types.: (GHC.Types.: d2DX GHC.Types.[]) == true
 && lqdc##$select##GHC.Types.:##1 (GHC.Types.: d2DX GHC.Types.[]) == d2DX
 && lqdc##$select##GHC.Types.:##2 (GHC.Types.: d2DX GHC.Types.[]) == GHC.Types.[]
 && is$GHC.Types.[] (GHC.Types.: d2DX GHC.Types.[]) == false
 && is$GHC.Types.: (GHC.Types.: d2DX GHC.Types.[]) == true
 && lqdc##$select##GHC.Types.:##1 (GHC.Types.: d2DX GHC.Types.[]) == d2DX
 && lqdc##$select##GHC.Types.:##2 (GHC.Types.: d2DX GHC.Types.[]) == GHC.Types.[]
 && head (GHC.Types.: d2DX GHC.Types.[]) == d2DX
 && tail (GHC.Types.: d2DX GHC.Types.[]) == GHC.Types.[])