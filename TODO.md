# TODO

tests/todo/elim00.min.fq

why **two** separate bindings


k362 has VV361 but we

+ "substitute" i.e. equate it with wink#ax3
+ AND then existentially quantify it
+ causing the info to be lost,
+ as the INNER wink#ax3 /= OUTER wink#ax3

```
bind 34 wink##ax3 : {VV##361 : int | [$k_##362]}

bind 45 wink##ax3 : {lq_tmp$x##452 : int | [$k_##428[lq_tmp$x##425:=wink##ax3][lq_tmp$x##456:=lq_anf$##dxy][VV##427:=lq_tmp$x##452][lq_tmp$x##426:=cow##ax4][lq_tmp$x##450:=lq_anf$##dxy][lq_tmp$x##430:=lq_tmp$x##452][lq_tmp$x##446:=lq_tmp$x##452][lq_tmp$x##422:=lq_anf$##dxy]]}
```

the solutions are the same! (almost)

```
$k_##362 := VV##361 == xig##awy

$k_##428 := VV##427 == wink##ax3
            && VV##427 == xig##awy
```

Yet  

+ `bind 34` used by `constraint id 1`

+ `bind 45` used by `constraint id 3`

which are connected by

  $k#444  

defined in

  id 3

and used in

  bind 48 wink##awA : {VV##443 : int | [$k_##444]}

which appears in env in

  id 1

which solves to:

  $k_##444 := VV##443 == xig##awy
            && VV##443 == wink##ax3

wf:
  env [0;
       1;
       2;
       3;
       4;
       5;
       6;
       7;
       8;
       9;
       10;
       11;
       12;
       13;
       14;
       15;
       16;
       17;
       28;

       34; // this is the CORRECT binding (per use-site)
           // but in the DEFINING constraint id 3
           // we have a DIFFERENT binder 45 and no explicit substitution!!!

       40;
       42]
  reft {VV##443 : int | [$k_##444]}
  // META wf : ()


----

ghc -ddump-ds -dno-suppress-uniques tests/pos/elim00.hs

foo :: Foo -> Foo
foo =
  \ ds_dmz  ->
    case ds_dmz of { Foo xig_alO yog_alP ->
      let ds_dmE = let ds_dmD   = (xig_alO, yog_alP)
                       cow_amq  = case ds_dmD of { (_, cow_amq) -> cow_amq }
                       wink_amp = case ds_dmD of { (wink_amp, _ ) -> wink_amp }  
                   in
                      (wink_amp, cow_amq)  
      in
        Elim.Foo
          (case ds_dmE of { (wink_amp, _) -> wink_amp })
          (case ds_dmE of { (_ , cow_amq) -> cow_amq  })

    }


          foo =
            \ (ds_dmz :: Foo) ->
              case ds_dmz of _ [Occ=Dead] { Foo xig_alO yog_alP ->
              let {
                ds_dmE :: (Int, Int)
                [LclId, Str=DmdType]
                ds_dmE =
                  let {
                    ds_dmD :: (Int, Int)
                    [LclId, Str=DmdType]
                    ds_dmD = (xig_alO, yog_alP) } in
                  let {
                    cow_amq :: Int
                    [LclId, Str=DmdType]
                    cow_amq =
                      case ds_dmD of _ [Occ=Dead] { (_ [Occ=Dead], cow_amq) ->
                      cow_amq
                      } } in
                  let {
                    wink_amp :: Int
                    [LclId, Str=DmdType]
                    wink_amp =
                      case ds_dmD of _ [Occ=Dead] { (wink_amp, _ [Occ=Dead]) ->
                      wink_amp
                      } } in
                  (wink_amp, cow_amq) } in
              Elim.Foo
                (case ds_dmE of _ [Occ=Dead] { (wink_amp, _ [Occ=Dead]) ->
                 wink_amp
                 })
                (case ds_dmE of _ [Occ=Dead] { (_ [Occ=Dead], cow_amq) ->
                 cow_amq
                 })
              }





Computing Result
UNSAT id 2 True
LHS: exists [lq_karg$v0##k0 : [(Tuple  int  a)];
             VV##2 : [(Tuple  int  a)];
             v2 : [(Tuple  int  a)]]
       . (lq_karg$v0##k0 == VV##2
          && v2 == VV##2)
         && exists [y : [(Tuple  int  a)]; VV##1 : [(Tuple  int  a)]]
              . (len y >= 0
                 && VV##1 == y)
                && lq_karg$v0##k0 == VV##1
RHS: len VV##2 >= 0
Unsafe [Just 2]
