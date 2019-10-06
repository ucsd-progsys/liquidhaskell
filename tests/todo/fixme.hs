{-@ LIQUID "--reflection"  @-}

module Labels where
import Language.Haskell.Liquid.Equational 
{-@ class measure Labels.canFlowTo :: forall l . l -> l -> Bool @-}
{-@ class measure Labels.join :: forall l . l -> l -> l @-}
{-@ class measure Labels.meet :: forall l . l -> l -> l @-}
{-@ class measure Labels.bot :: forall l . l @-}
{-@ class Label l where
      canFlowTo :: a : l -> b : l -> {v : Bool | v == Labels.canFlowTo a b}
      meet :: a : l -> b : l -> {v : l | v == Labels.meet a b}
      join :: a : l -> b : l -> {v : l | v == Labels.join a b}
      bot  :: {v:l | v == Labels.bot } 

      lawFlowReflexivity :: l : l -> {v : () | Labels.canFlowTo l l}
      lawFlowAntisymmetry :: a : l -> {b : l | Labels.canFlowTo a b && canFlowTo b a} -> {v : () | a == b}
      lawFlowTransitivity :: a:l -> b:l-> c:l -> {(Labels.canFlowTo a b && Labels.canFlowTo b c) => canFlowTo a c}

      lawMeet :: z : l -> x : l -> y : l -> w : l -> {z == Labels.meet x y => (Labels.canFlowTo z x && canFlowTo z y && ((canFlowTo w x && canFlowTo w y) => canFlowTo w z))}
      lawJoin :: z : l -> x : l -> y : l -> w : l -> {z == Labels.join x y => (Labels.canFlowTo x z && canFlowTo y z && ((canFlowTo x w && canFlowTo y w) => canFlowTo z w))}
      lawBot  :: x : l -> { Labels.canFlowTo Labels.bot x }
@-}
class Label l where
    canFlowTo :: l-> l -> Bool
    meet :: l -> l -> l
    join :: l -> l -> l
    bot  :: l 

    lawFlowReflexivity :: l -> ()
    lawFlowAntisymmetry :: l -> l -> ()
    lawFlowTransitivity :: l -> l -> l -> ()

    lawMeet :: l -> l -> l -> l -> ()
    lawJoin :: l -> l -> l -> l -> ()
    lawBot  :: l -> ()

{-@ joinCanFlowTo 
 :: Label l
 => l1 : l
 -> l2 : l
 -> l3 : l
 -> {canFlowTo l1 l3 && canFlowTo l2 l3 <=> canFlowTo (join l1 l2) l3}
 @-}
joinCanFlowTo :: Label l => l -> l -> l -> ()
joinCanFlowTo l1 l2 l3 = lawJoin (join l1 l2) l1 l2 l3 &&& unjoinCanFlowTo l1 l2 l3 


{-@ unjoinCanFlowTo 
 :: Label l
 => l1:l -> l2:l -> l3:l 
 -> {canFlowTo (join l1 l2) l3 => (canFlowTo l1 l3  && canFlowTo l2 l3)}
 @-}
unjoinCanFlowTo :: Label l => l -> l -> l -> ()
unjoinCanFlowTo l1 l2 l3 
  =     lawJoin (join l1 l2) l1 l2 l3  
    &&& lawFlowTransitivity l1 (l1 `join` l2) l3 
    &&& lawFlowTransitivity l2 (l1 `join` l2) l3 

{-@ notJoinCanFlowTo 
 :: Label l 
 => a : l 
 -> b : l 
 -> c : {l | not (canFlowTo a c)}
 -> {not (canFlowTo (join a b) c)}
 @-}
notJoinCanFlowTo :: Label l => l -> l -> l -> ()
notJoinCanFlowTo l1 l2 l3 = unjoinCanFlowTo l1 l2 l3

{-@ notCanFlowTo 
 :: Label l 
 => a : l 
 -> b : l 
 -> c : l
 -> {not (canFlowTo b a) && canFlowTo b c => not (canFlowTo c a)}
 @-}
notCanFlowTo :: Label l => l -> l -> l -> ()
notCanFlowTo a b c 
  | b `canFlowTo` c 
  = lawFlowTransitivity b c a  
notCanFlowTo a b c 
  = ()

unjoinCanFlowToItself :: Label l => l -> l -> ()
{-@ unjoinCanFlowToItself :: Label l => a:l -> b:l 
  -> { canFlowTo a (join a b) && canFlowTo b (join a b) } @-}
unjoinCanFlowToItself x y = lawJoin (x `join` y) x y x   