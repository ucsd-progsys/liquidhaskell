{-@ LIQUID "--expect-error-containing=Negative occurence of PositivityCheck.Bad1" @-}
{-@ LIQUID "--expect-error-containing=Negative occurence of PositivityCheck.Bad2" @-}
{-@ LIQUID "--expect-error-containing=Negative occurence of PositivityCheck.Bad3" @-}
{-@ LIQUID "--expect-error-containing=Negative occurence of PositivityCheck.Bad4" @-}
{-@ LIQUID "--expect-error-containing=Negative occurence of PositivityCheck.BadRec1" @-}
{-@ LIQUID "--expect-error-containing=Negative occurence of PositivityCheck.BadRec2" @-}
module PositivityCheck where

data Bad1 a = No11 (Bad1 a -> Int) | No12 (Bad1 a) 
data Bad2 a = No2 (Int -> Bad2 a -> Int)
data Bad3 a = No3 (Bad3 Int -> Int)
data Bad4 a = Bar (Flip (Flip (Flip (Bad4 a))))
type Flip a = a -> Int 

data BadRec1 a = NoRec1 (BadRec2 a -> Int)
data BadRec2 a = NoRec2 (BadRec1 a)
