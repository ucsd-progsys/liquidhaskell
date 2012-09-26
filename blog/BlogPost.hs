#!/usr/bin/env runhaskell

-- | Trivial script that posts to a URL using BlogLiterately.

import System.Console.CmdArgs                   (cmdArgs)
import Text.BlogLiterately.Options
import Text.BlogLiterately.Post                 (postIt)


main = do opts <- cmdArgs blOpts 
          html <- readFile $ file opts 
          postIt opts html 
