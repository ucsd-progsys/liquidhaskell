module TerminationExpr where

{-@ showSep :: _ -> xs:_ -> _ / [len ys] @-} -- use xs as reducing param
showSep :: String -> [String] -> String
showSep sep []     = ""
showSep sep [x]    = x
showSep sep (x:xs) = x ++ sep ++ showSep sep xs

