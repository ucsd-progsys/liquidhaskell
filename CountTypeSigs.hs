#!/usr/bin/env stack
-- stack runhaskell --resolver lts-9.6 --package haskell-src-exts-1.19.1
import Language.Haskell.Exts.Extension
import Language.Haskell.Exts.Parser
import Language.Haskell.Exts.SrcLoc
import Language.Haskell.Exts.Syntax
import System.Environment

themod file =
  parseModuleWithMode
    (defaultParseMode
       { extensions = [ EnableExtension ExplicitForAll
                      , EnableExtension TypeFamilies
                      , EnableExtension MultiParamTypeClasses
                      , EnableExtension FlexibleContexts
                      , EnableExtension EmptyCase
                      , EnableExtension ConstraintKinds
                      , EnableExtension TemplateHaskell
                      , EnableExtension TypeOperators
                      , EnableExtension ScopedTypeVariables
                      , EnableExtension ExistentialQuantification
                      , EnableExtension BangPatterns
                      , EnableExtension DataKinds
                      ]
       , fixities = Just []
       })
    <$> readFile file

main = do
  file <- head <$> getArgs
  mod <- themod file
  let decls = ((\(Module _ _ _ _ x) -> x) . \(ParseOk x) -> x) mod
  print $
    sum $
      map (\(TypeSig x _ _) -> (rect . fst . spanSize . srcInfoSpan) x) $
        filter isTypeSig decls

isTypeSig TypeSig{} = True
isTypeSig _         = False

-- Single line typesigs are reported as height zero
rect 0 = 1
rect x = x + 1
