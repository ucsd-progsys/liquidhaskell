# TODO

tests/todo/elim00.min.fq

why **two** separate bindings

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
