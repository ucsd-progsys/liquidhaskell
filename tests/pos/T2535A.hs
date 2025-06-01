{-@ LIQUID "--reflection"     @-}

module T2535A where

infixl 3 ?

{-@ (?) :: forall a b <pa :: a -> Bool, pb :: b -> Bool>. a<pa> -> b<pb> -> a<pa> @-}
(?) :: a -> b -> a
x ? _ = x

{-@ foo :: () -> {1 + 2 == 3} @-}
foo :: () -> () 
foo () =  () ? ( () ? )  

{-

When compiled with GHC, this will produce the CORE :

Foo.foo
  = \ (ds_dL9 :: ()) ->
      src<src/Foo.hs:(36,1)-(37,17)>
      case ds_dL9 of { () ->
      src<src/Foo.hs:37:6-17>
      Foo.?
        @()
        @(GHC.Types.ZonkAny 0 -> ())
        (src<src/Foo.hs:37:6-7> GHC.Tuple.())
        (src<src/Foo.hs:37:11-17>
        (Foo.?
                 @()
                 @(GHC.Types.ZonkAny 0)
                 (src<src/Foo.hs:37:13-14> GHC.Tuple.()))
      },

For some reason, when compiled in a cabal project,
the produced CORE (before LH processing) is eta expanded:

Foo.foo
  = \ (ds_dL9 :: ()) ->
      src<src/Foo.hs:(36,1)-(37,17)>
      case ds_dL9 of { () ->
      src<src/Foo.hs:37:6-17>
      Foo.?
        @()
        @(GHC.Types.ZonkAny 0 -> ())
        (src<src/Foo.hs:37:6-7> GHC.Tuple.())
        (src<src/Foo.hs:37:11-17>
         let {
           v_B1 :: GHC.Types.ZonkAny 0 -> ()
           [LclId,
            Unf=Unf{Src=<vanilla>, TopLvl=False,
                    Value=False, ConLike=False, WorkFree=False, Expandable=False,
                    Guidance=IF_ARGS [] 20 0}]
           v_B1
             = Foo.?
                 @()
                 @(GHC.Types.ZonkAny 0)
                 (src<src/Foo.hs:37:13-14> GHC.Tuple.()) } in
         \ (v_B2 :: GHC.Types.ZonkAny 0) -> v_B1 v_B2)
      },

This produces a lambda argument with type `Zonk Any 0` (existential types 
that can have different kinds)

Language.Haskell.Liquid.Constraint.Generate.addFunctionConstraint
will generate a signleton type 

```
"dPkh" {VV : func(0 , [(GHC.Types.ZonkAny (GHC.Prim.TYPE (GHC.Types.BoxedRep GHC.Types.Lifted)) int);
                    Tuple0]) | [(VV =
                                   lam lam_arg##1 : (GHC.Types.ZonkAny (GHC.Prim.TYPE (GHC.Types.BoxedRep GHC.Types.Lifted)) fix$36$0) . (v_B1 ((lam_arg##1  :  (GHC.Types.ZonkAny (GHC.Prim.TYPE (GHC.Types.BoxedRep GHC.Types.Lifted)) fix$36$0))  :  (GHC.Types.ZonkAny (GHC.Prim.TYPE (GHC.Types.BoxedRep GHC.Types.Lifted)) fix$36$0))))]} failed on:
        VV == lam lam_arg##1 : (GHC.Types.ZonkAny (GHC.Prim.TYPE (GHC.Types.BoxedRep GHC.Types.Lifted)) fix$36$0) . v_B1 ((lam_arg##1 : (GHC.Types.ZonkAny (GHC.Prim.TYPE (GHC.Types.BoxedRep GHC.Types.Lifted)) fix$36$0)) : (GHC.Types.ZonkAny (GHC.Prim.TYPE (GHC.Types.BoxedRep GHC.Types.Lifted)) fix$36$0))
```

The problem is that there is an inconsistency in a way that LH (or GHC) sees the ZonkAny type.
It can be seen as either as `ZonkAny * 0` or as `ZonkAny * Int`. 

Thus elaboration crashes with `Cannot unify int with fix$36$0`. 


To address this, 
`Language.Haskell.Liquid.Types.RefType.tyConFTyCon` ignores the nat argument 
of the ZonkAny type and encodes the type `ZonkAny * 0` just as as `ZonkAny`.
This is better, since LH should not care about the kind of the existential types, 
thus the information passed seems more relevant.


(This bug inconsistncy appeared since with the rest edits of this PR the types 
of the functions are explicitly entered in the logic.)
-}