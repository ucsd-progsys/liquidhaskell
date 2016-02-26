# TODO


failing tests

## hangs

../liquid-fixpoint/tests/todo/

## fails

rec_annot_go.hs:                              FAIL (0.98s)
selfList.hs:                                  FAIL (1.07s)
test00c.hs:                                   FAIL (1.20s)
vector1.hs:                                   FAIL (1.33s)
vector2.hs:                                   FAIL (2.05s)
  -- unbound symbol

wrap0.hs:                                     FAIL (0.98s)
wrap1.hs:                                     FAIL (1.58s)
vector1a.hs:                                  FAIL (1.65s)
vector1b.hs:                                  FAIL (1.33s)
take.hs:                                      FAIL (1.31s)
  -- cannot unify aXXX with aYYY

----


(exists [lq_karg$VV##258##k_##259 : int;
         lq_karg$GHC.Types.False##68##k_##259 : GHC.Types.Bool;
         lq_karg$GHC.Classes.$fOrdInt##rni##k_##259 : (GHC.Classes.Ord  int);
         lq_karg$GHC.Types.EQ##6U##k_##259 : GHC.Types.Ordering;
         lq_karg$x##a127##k_##259 : int;
         lq_karg$fix$36$$36$dNum_a12w##k_##259 : (GHC.Num.Num  int);
         lq_tmp$x##344 : int;
         lq_karg$fix$36$$36$dOrd_a12x##k_##259 : (GHC.Classes.Ord  int);
         lq_karg$GHC.Num.$fNumInt##rma##k_##259 : (GHC.Num.Num  int);
         lq_karg$GHC.Types.GT##6W##k_##259 : GHC.Types.Ordering;
         lq_karg$GHC.Types.True##6u##k_##259 : GHC.Types.Bool;
         lq_karg$GHC.Types.LT##6S##k_##259 : GHC.Types.Ordering]
   . (lq_karg$VV##258##k_##259 == lq_anf$##d13h
      && lq_karg$GHC.Types.False##68##k_##259 == GHC.Types.False##68
      && lq_karg$GHC.Classes.$fOrdInt##rni##k_##259 == GHC.Classes.$fOrdInt##rni
      && lq_karg$GHC.Types.EQ##6U##k_##259 == GHC.Types.EQ##6U
      && lq_karg$x##a127##k_##259 == n1##a128
      && lq_karg$fix$36$$36$dNum_a12w##k_##259 == GHC.Num.$fNumInt##rma
      && lq_tmp$x##344 == lq_anf$##d13h
      && lq_karg$fix$36$$36$dOrd_a12x##k_##259 == GHC.Classes.$fOrdInt##rni
      && lq_karg$GHC.Num.$fNumInt##rma##k_##259 == GHC.Num.$fNumInt##rma
      && lq_karg$GHC.Types.GT##6W##k_##259 == GHC.Types.GT##6W
      && lq_karg$GHC.Types.True##6u##k_##259 == GHC.Types.True##6u
      && lq_karg$GHC.Types.LT##6S##k_##259 == GHC.Types.LT##6S
      && lq_karg$a_a12v##k_##259 == a_a12v)
     && exists [fix$36$$36$dNum_a12w : (GHC.Num.Num  a_a12v);
                a_a12v : num;
                fix$36$$36$dOrd_a12x : (GHC.Classes.Ord  a_a12v);
                x##a127 : a_a12v;
                VV##7 : a_a12v;
                lq_anf$##d13a : int;
                lq_anf$##d13b : a_a12v;
                lq_anf$##d13c : GHC.Types.Bool;
                lq_anf$##d13d : GHC.Types.Bool;
                lq_anf$##d13d : GHC.Types.Bool;
                lq_anf$##d13d : GHC.Types.Bool;
                lq_anf$##d13e : int;
                lq_anf$##d13f : a_a12v]
          . (exists [lq_karg$VV##254##k_##255 : a_a12v;
                     lq_karg$GHC.Types.EQ##6U##k_##255 : GHC.Types.Ordering;
                     lq_karg$GHC.Types.GT##6W##k_##255 : GHC.Types.Ordering;
                     lq_karg$GHC.Types.False##68##k_##255 : GHC.Types.Bool;
                     lq_karg$GHC.Num.$fNumInt##rma##k_##255 : (GHC.Num.Num  int);
                     lq_karg$GHC.Types.True##6u##k_##255 : GHC.Types.Bool;
                     lq_karg$GHC.Types.LT##6S##k_##255 : GHC.Types.Ordering;
                     lq_karg$a_a12v##k_##255 : num;
                     lq_karg$fix$36$$36$dNum_a12w##k_##255 : (GHC.Num.Num  a_a12v);
                     lq_karg$fix$36$$36$dOrd_a12x##k_##255 : (GHC.Classes.Ord  a_a12v);
                     VV##254 : a_a12v;
                     lq_karg$GHC.Classes.$fOrdInt##rni##k_##255 : (GHC.Classes.Ord  int)]
               . (lq_karg$VV##254##k_##255 == x##a127
                  && lq_karg$GHC.Types.EQ##6U##k_##255 == GHC.Types.EQ##6U
                  && lq_karg$GHC.Types.GT##6W##k_##255 == GHC.Types.GT##6W
                  && lq_karg$GHC.Types.False##68##k_##255 == GHC.Types.False##68
                  && lq_karg$GHC.Num.$fNumInt##rma##k_##255 == GHC.Num.$fNumInt##rma
                  && lq_karg$GHC.Types.True##6u##k_##255 == GHC.Types.True##6u
                  && lq_karg$GHC.Types.LT##6S##k_##255 == GHC.Types.LT##6S
                  && lq_karg$a_a12v##k_##255 == a_a12v
                  && lq_karg$fix$36$$36$dNum_a12w##k_##255 == fix$36$$36$dNum_a12w
                  && lq_karg$fix$36$$36$dOrd_a12x##k_##255 == fix$36$$36$dOrd_a12x
                  && VV##254 == x##a127
                  && lq_karg$GHC.Classes.$fOrdInt##rni##k_##255 == GHC.Classes.$fOrdInt##rni)
                 && exists [VV##5 : int]
                      . VV##5 == n1##a128
                        && (lq_karg$VV##254##k_##255 == VV##5
                            && lq_karg$GHC.Types.EQ##6U##k_##255 == GHC.Types.EQ##6U
                            && lq_karg$GHC.Types.GT##6W##k_##255 == GHC.Types.GT##6W
                            && lq_karg$GHC.Types.False##68##k_##255 == GHC.Types.False##68
                            && lq_karg$GHC.Num.$fNumInt##rma##k_##255 == GHC.Num.$fNumInt##rma
                            && lq_karg$GHC.Types.True##6u##k_##255 == GHC.Types.True##6u
                            && lq_karg$GHC.Types.LT##6S##k_##255 == GHC.Types.LT##6S
                            && lq_karg$fix$36$$36$dNum_a12w##k_##255 == GHC.Num.$fNumInt##rma
                            && lq_karg$fix$36$$36$dOrd_a12x##k_##255 == GHC.Classes.$fOrdInt##rni
                            && lq_karg$GHC.Classes.$fOrdInt##rni##k_##255 == GHC.Classes.$fOrdInt##rni)
             && VV##7 == lq_anf$##d13f - x##a127
             && lq_anf$##d13a == 0
             && lq_anf$##d13b == lq_anf$##d13a
             && (Prop lq_anf$##d13c <=> x##a127 > lq_anf$##d13b)
             && lq_anf$##d13d == lq_anf$##d13c
             && lq_anf$##d13d == lq_anf$##d13c
             && (lq_anf$##d13d == lq_anf$##d13c
                 && not (Prop lq_anf$##d13d)
                 && not (Prop lq_anf$##d13d)
                 && not (Prop lq_anf$##d13d))
             && lq_anf$##d13e == 0
             && lq_anf$##d13f == lq_anf$##d13e)
            && (lq_karg$VV##258##k_##259 == VV##7
                && lq_karg$GHC.Types.False##68##k_##259 == GHC.Types.False##68
                && lq_karg$GHC.Classes.$fOrdInt##rni##k_##259 == GHC.Classes.$fOrdInt##rni
                && lq_karg$GHC.Types.EQ##6U##k_##259 == GHC.Types.EQ##6U
                && lq_karg$x##a127##k_##259 == x##a127
                && lq_karg$fix$36$$36$dNum_a12w##k_##259 == fix$36$$36$dNum_a12w
                && lq_karg$fix$36$$36$dOrd_a12x##k_##259 == fix$36$$36$dOrd_a12x
                && lq_karg$GHC.Num.$fNumInt##rma##k_##259 == GHC.Num.$fNumInt##rma
                && lq_karg$GHC.Types.GT##6W##k_##259 == GHC.Types.GT##6W
                && lq_karg$GHC.Types.True##6u##k_##259 == GHC.Types.True##6u
                && lq_karg$GHC.Types.LT##6S##k_##259 == GHC.Types.LT##6S)
 || exists [lq_karg$VV##258##k_##259 : int;
            lq_karg$GHC.Types.False##68##k_##259 : GHC.Types.Bool;
            lq_karg$GHC.Classes.$fOrdInt##rni##k_##259 : (GHC.Classes.Ord  int);
            lq_karg$GHC.Types.EQ##6U##k_##259 : GHC.Types.Ordering;
            lq_karg$x##a127##k_##259 : int;
            lq_karg$fix$36$$36$dNum_a12w##k_##259 : (GHC.Num.Num  int);
            lq_tmp$x##344 : int;
            lq_karg$fix$36$$36$dOrd_a12x##k_##259 : (GHC.Classes.Ord  int);
            lq_karg$GHC.Num.$fNumInt##rma##k_##259 : (GHC.Num.Num  int);
            lq_karg$GHC.Types.GT##6W##k_##259 : GHC.Types.Ordering;
            lq_karg$GHC.Types.True##6u##k_##259 : GHC.Types.Bool;
            lq_karg$GHC.Types.LT##6S##k_##259 : GHC.Types.Ordering]
      . (lq_karg$VV##258##k_##259 == lq_anf$##d13h
         && lq_karg$GHC.Types.False##68##k_##259 == GHC.Types.False##68
         && lq_karg$GHC.Classes.$fOrdInt##rni##k_##259 == GHC.Classes.$fOrdInt##rni
         && lq_karg$GHC.Types.EQ##6U##k_##259 == GHC.Types.EQ##6U
         && lq_karg$x##a127##k_##259 == n1##a128
         && lq_karg$fix$36$$36$dNum_a12w##k_##259 == GHC.Num.$fNumInt##rma
         && lq_tmp$x##344 == lq_anf$##d13h
         && lq_karg$fix$36$$36$dOrd_a12x##k_##259 == GHC.Classes.$fOrdInt##rni
         && lq_karg$GHC.Num.$fNumInt##rma##k_##259 == GHC.Num.$fNumInt##rma
         && lq_karg$GHC.Types.GT##6W##k_##259 == GHC.Types.GT##6W
         && lq_karg$GHC.Types.True##6u##k_##259 == GHC.Types.True##6u
         && lq_karg$GHC.Types.LT##6S##k_##259 == GHC.Types.LT##6S
         && lq_karg$a_a12v##k_##259 == a_a12v)
        && exists [fix$36$$36$dNum_a12w : (GHC.Num.Num  a_a12v);
                   a_a12v : num;
                   fix$36$$36$dOrd_a12x : (GHC.Classes.Ord  a_a12v);
                   VV##6 : a_a12v;
                   x##a127 : a_a12v;
                   lq_anf$##d13a : int;
                   lq_anf$##d13b : a_a12v;
                   lq_anf$##d13c : GHC.Types.Bool;
                   lq_anf$##d13d : GHC.Types.Bool;
                   lq_anf$##d13d : GHC.Types.Bool;
                   lq_anf$##d13d : GHC.Types.Bool]
             . (VV##6 == x##a127
                && exists [lq_karg$VV##254##k_##255 : a_a12v;
                           lq_karg$GHC.Types.EQ##6U##k_##255 : GHC.Types.Ordering;
                           lq_karg$GHC.Types.GT##6W##k_##255 : GHC.Types.Ordering;
                           lq_karg$GHC.Types.False##68##k_##255 : GHC.Types.Bool;
                           lq_karg$GHC.Num.$fNumInt##rma##k_##255 : (GHC.Num.Num  int);
                           lq_karg$GHC.Types.True##6u##k_##255 : GHC.Types.Bool;
                           lq_karg$GHC.Types.LT##6S##k_##255 : GHC.Types.Ordering;
                           lq_karg$a_a12v##k_##255 : num;
                           lq_karg$fix$36$$36$dNum_a12w##k_##255 : (GHC.Num.Num  a_a12v);
                           lq_karg$fix$36$$36$dOrd_a12x##k_##255 : (GHC.Classes.Ord  a_a12v);
                           VV##254 : a_a12v;
                           lq_karg$GHC.Classes.$fOrdInt##rni##k_##255 : (GHC.Classes.Ord  int)]
                     . (lq_karg$VV##254##k_##255 == x##a127
                        && lq_karg$GHC.Types.EQ##6U##k_##255 == GHC.Types.EQ##6U
                        && lq_karg$GHC.Types.GT##6W##k_##255 == GHC.Types.GT##6W
                        && lq_karg$GHC.Types.False##68##k_##255 == GHC.Types.False##68
                        && lq_karg$GHC.Num.$fNumInt##rma##k_##255 == GHC.Num.$fNumInt##rma
                        && lq_karg$GHC.Types.True##6u##k_##255 == GHC.Types.True##6u
                        && lq_karg$GHC.Types.LT##6S##k_##255 == GHC.Types.LT##6S
                        && lq_karg$a_a12v##k_##255 == a_a12v
                        && lq_karg$fix$36$$36$dNum_a12w##k_##255 == fix$36$$36$dNum_a12w
                        && lq_karg$fix$36$$36$dOrd_a12x##k_##255 == fix$36$$36$dOrd_a12x
                        && VV##254 == x##a127
                        && lq_karg$GHC.Classes.$fOrdInt##rni##k_##255 == GHC.Classes.$fOrdInt##rni)
                       && exists [VV##5 : int]
                            . VV##5 == n1##a128
                              && (lq_karg$VV##254##k_##255 == VV##5
                                  && lq_karg$GHC.Types.EQ##6U##k_##255 == GHC.Types.EQ##6U
                                  && lq_karg$GHC.Types.GT##6W##k_##255 == GHC.Types.GT##6W
                                  && lq_karg$GHC.Types.False##68##k_##255 == GHC.Types.False##68
                                  && lq_karg$GHC.Num.$fNumInt##rma##k_##255 == GHC.Num.$fNumInt##rma
                                  && lq_karg$GHC.Types.True##6u##k_##255 == GHC.Types.True##6u
                                  && lq_karg$GHC.Types.LT##6S##k_##255 == GHC.Types.LT##6S
                                  && lq_karg$fix$36$$36$dNum_a12w##k_##255 == GHC.Num.$fNumInt##rma
                                  && lq_karg$fix$36$$36$dOrd_a12x##k_##255 == GHC.Classes.$fOrdInt##rni
                                  && lq_karg$GHC.Classes.$fOrdInt##rni##k_##255 == GHC.Classes.$fOrdInt##rni)
                && lq_anf$##d13a == 0
                && lq_anf$##d13b == lq_anf$##d13a
                && (Prop lq_anf$##d13c <=> x##a127 > lq_anf$##d13b)
                && lq_anf$##d13d == lq_anf$##d13c
                && lq_anf$##d13d == lq_anf$##d13c
                && (lq_anf$##d13d == lq_anf$##d13c
                    && Prop lq_anf$##d13d
                    && Prop lq_anf$##d13d
                    && Prop lq_anf$##d13d))
               && (lq_karg$VV##258##k_##259 == VV##6
                   && lq_karg$GHC.Types.False##68##k_##259 == GHC.Types.False##68
                   && lq_karg$GHC.Classes.$fOrdInt##rni##k_##259 == GHC.Classes.$fOrdInt##rni
                   && lq_karg$GHC.Types.EQ##6U##k_##259 == GHC.Types.EQ##6U
                   && lq_karg$x##a127##k_##259 == x##a127
                   && lq_karg$fix$36$$36$dNum_a12w##k_##259 == fix$36$$36$dNum_a12w
                   && lq_karg$fix$36$$36$dOrd_a12x##k_##259 == fix$36$$36$dOrd_a12x
                   && lq_karg$GHC.Num.$fNumInt##rma##k_##259 == GHC.Num.$fNumInt##rma
                   && lq_karg$GHC.Types.GT##6W##k_##259 == GHC.Types.GT##6W
                   && lq_karg$GHC.Types.True##6u##k_##259 == GHC.Types.True##6u
                   && lq_karg$GHC.Types.LT##6S##k_##259 == GHC.Types.LT##6S))
&& VV##2 == lq_anf$##d13j
&& lq_anf$##d13i == (0 : int)
&& (Prop lq_anf$##d13j <=> lq_anf$##d13h >= lq_anf$##d13i)
&& Prop GHC.Types.True##6u
&& not (Prop GHC.Types.False##68)
&& not (Prop GHC.Types.False##68)
&& Prop GHC.Types.True##6u
&& cmp GHC.Types.GT##6W == GHC.Types.GT##6W
&& cmp GHC.Types.LT##6S == GHC.Types.LT##6S
&& cmp GHC.Types.EQ##6U == GHC.Types.EQ##6U
&& lq_anf$##d13g == (0 : int)
with error
Unbound Symbol lq_karg$a_a12v##k_##259
Perhaps you meant: lq_karg$x##a127##k_##259
