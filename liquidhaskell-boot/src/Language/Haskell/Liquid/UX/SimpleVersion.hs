{-# LANGUAGE TemplateHaskell #-}

module Language.Haskell.Liquid.UX.SimpleVersion (simpleVersion) where

import Data.Version (Version, showVersion)
import GitHash (GitInfo, giDirty, giHash, tGitInfoCwdTry)
import Language.Haskell.TH (Exp, Q)
import qualified Language.Haskell.TH.Syntax as TH.Syntax
import qualified Language.Haskell.TH.Syntax.Compat as TH.Syntax.Compat

-- | Generate a string like @Version 1.2, Git revision 1234@.
--
-- @$(simpleVersion …)@ @::@ 'String'
-- Taken from <https://hackage.haskell.org/package/optparse-simple-0.1.1.4/docs/Options-Applicative-Simple.html#v:simpleVersion>
-- so we can drop the dependency on optparse-simple.
simpleVersion :: Version -> Q Exp
simpleVersion version =
  [|
    concat
      ( [ "Version ",
          $(TH.Syntax.lift $ showVersion version)
        ]
          ++ case $(TH.Syntax.Compat.unTypeSplice tGitInfoCwdTry) :: Either String GitInfo of
            Left _ -> []
            Right gi ->
              [ ", Git revision ",
                giHash gi,
                if giDirty gi then " (dirty)" else ""
              ]
      )
    |]
