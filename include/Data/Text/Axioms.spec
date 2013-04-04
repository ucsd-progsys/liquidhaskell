module spec Data.Text.Axioms where


axiom_numchars_append
  :: a:Text -> b:Text -> t:Text
  -> {v:Bool | ((Prop v) <=> (((tlen t) = (tlen a) + (tlen b))
                              => ((tlength t) = (tlength a) + (tlength b))))}

-- FIXME: I don't like the replicate and init axioms.. they only hold when
-- t2 is generated from t1
axiom_numchars_replicate
  :: t1:Text -> t2:Text
  -> {v:Bool | ((Prop v) <=> (((tlen t2) >= (tlen t1))
                              => ((tlength t2) >= (tlength t1))))}

axiom_numchars_init
  :: t1:Text -> t2:Text
  -> {v:Bool | ((Prop v) <=> (((tlen t2) < (tlen t1))
                              => ((tlength t2) < (tlength t1))))}

axiom_numchars_split
  :: t:Text
  -> i:Int
  -> {v:Bool | ((Prop v) <=>
                ((numchars (tarr t) (toff t) (tlen t))
                 = ((numchars (tarr t) (toff t) i)
                    + (numchars (tarr t) ((toff t) + i) ((tlen t) - i)))))}


nc :: a:A.Array -> o:Int -> l:Int -> {v:Int | v = (numchars a o l)}
tl :: t:Text -> {v:Int | v = (tlength t)}
