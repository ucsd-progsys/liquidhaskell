module spec GHC.Read where

type ParsedString XS =  {v:_ | (if ((len XS) > 0) then ((len v) < (len XS)) else ((len v) = 0))}

GHC.Read.lex :: xs:_ -> [((ParsedString xs), (ParsedString xs))]
