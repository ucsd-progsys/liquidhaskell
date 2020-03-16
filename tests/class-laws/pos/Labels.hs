{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--oldple"     @-}
module Labels where 

class Label l where 
  canFlowTo :: l -> l -> Bool 
  meet      :: l -> l -> l 
  join      :: l -> l -> l 
  bot       :: l 

{-@ class laws Label l where
      lawFlowReflexivity :: l : l -> { canFlowTo l l}
      lawFlowAntisymmetry :: a : l -> {b : l | canFlowTo a b && canFlowTo b a} -> {v : () | a == b}
      lawFlowTransitivity :: a:l -> b:l-> c:l -> {(canFlowTo a b && canFlowTo b c) => canFlowTo a c}

      lawMeet :: z : l -> x : l -> y : l -> w : l -> {z == meet x y => (canFlowTo z x && canFlowTo z y && ((canFlowTo w x && canFlowTo w y) => canFlowTo w z))}
      lawJoin :: z : l -> x : l -> y : l -> w : l -> {z == join x y => (canFlowTo x z && canFlowTo y z && ((canFlowTo x w && canFlowTo y w) => canFlowTo z w))}
      lawBot  :: x : l -> { canFlowTo bot x }
 @-}

lawFlowReflexivity  :: Label l => l -> ()
lawFlowReflexivity _ = ()
lawFlowAntisymmetry :: Label l => l -> l -> () 
lawFlowAntisymmetry _ _ = ()
lawFlowTransitivity :: Label l => l -> l -> l -> ()
lawFlowTransitivity _ _ _ = () 

lawMeet, lawJoin :: Label l => l -> l -> l -> l -> () 
lawMeet _ _ _ _ = () 
lawJoin _ _ _ _ = () 
lawBot  :: Label l => l -> ()
lawBot _ = ()


data HighLow = High | Low 

instance Label HighLow where 
  canFlowTo = canFlowToHL
  meet      = meetHL 
  join      = joinHL
  bot       = botHL

{-@
instance laws Label HighLow where 
  canFlowTo = canFlowToHL
  meet      = meetHL 
  join      = joinHL
  bot       = botHL

  lawFlowReflexivity  = lawFlowReflexivityHL
  lawFlowAntisymmetry = lawFlowAntisymmetryHL
  lawFlowTransitivity = lawFlowTransitivityHL


  lawMeet   = lawMeetHL
  lawJoin   = lawJoinHL
  lawBot    = lawBotHL
@-}


{-@ reflect canFlowToHL @-}
canFlowToHL :: HighLow -> HighLow -> Bool
canFlowToHL Low High  = True 
canFlowToHL Low Low   = True
canFlowToHL High High = True 
canFlowToHL High Low  = False 

{-@ reflect meetHL @-}
meetHL :: HighLow -> HighLow -> HighLow 
meetHL Low High  = Low 
meetHL Low Low   = Low
meetHL High High = High 
meetHL High Low  = Low 

{-@ reflect joinHL @-}
joinHL :: HighLow -> HighLow -> HighLow 
joinHL Low High  = High 
joinHL Low Low   = Low
joinHL High High = High 
joinHL High Low  = High 

{-@ reflect botHL @-}
botHL :: HighLow 
botHL = Low



-- Laws 

{-@ lawBotHL :: l:HighLow -> { canFlowToHL botHL l} @-}
lawBotHL Low  = () 
lawBotHL High = () 

{-@ lawFlowReflexivityHL:: l:HighLow -> { canFlowToHL l l} @-}
lawFlowReflexivityHL :: HighLow -> () 
lawFlowReflexivityHL _      = ()


{-@ lawFlowAntisymmetryHL :: a:HighLow -> b:{HighLow | canFlowToHL a b && canFlowToHL b a} -> { a == b } @-}
lawFlowAntisymmetryHL :: HighLow -> HighLow -> ()
lawFlowAntisymmetryHL _ _   = () 


{-@ lawFlowTransitivityHL :: a:HighLow -> b:HighLow -> c:HighLow 
  -> {(canFlowToHL a b && canFlowToHL b c) => canFlowToHL a c} @-}
lawFlowTransitivityHL :: HighLow -> HighLow -> HighLow -> ()
lawFlowTransitivityHL _ _ _ = () 


{-@ ple lawMeetHL @-}
{-@ lawMeetHL :: z:HighLow -> x:HighLow -> y:HighLow -> w:HighLow 
  -> { z == meetHL x y => (canFlowToHL z x && canFlowToHL z y && ((canFlowToHL w x && canFlowToHL w y) => canFlowToHL w z))} @-}
lawMeetHL :: HighLow -> HighLow -> HighLow -> HighLow -> () 
lawMeetHL _ _ _ _  = ()


{-@ ple lawJoinHL @-}
{-@ lawJoinHL :: z:HighLow -> x:HighLow -> y:HighLow -> w:HighLow 
  -> { z == joinHL x y => (canFlowToHL x z && canFlowToHL y z && ((canFlowToHL x w && canFlowToHL y w) => canFlowToHL z w))} @-}
lawJoinHL :: HighLow -> HighLow -> HighLow -> HighLow -> () 
lawJoinHL _ _ _ _ = () 