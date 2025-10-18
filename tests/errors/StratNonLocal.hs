{-@ LIQUID "--expect-error-containing=Unknown locally-defined type constructor `Maybe`" @-}
module StratNonLocal where
{-@ stratified Maybe @-}
