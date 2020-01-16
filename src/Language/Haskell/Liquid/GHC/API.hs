-- | This module re-exports a bunch of the GHC API.

module Language.Haskell.Liquid.GHC.API (module Ghc) where 

import GHC            as Ghc
import ConLike        as Ghc
import Var            as Ghc
import Module         as Ghc
import DataCon        as Ghc
import TysWiredIn     as Ghc  
import BasicTypes     as Ghc 
import CoreSyn        as Ghc hiding (AnnExpr, AnnExpr' (..), AnnRec, AnnCase) 
import TyCon          as Ghc 
import NameSet        as Ghc
import InstEnv        as Ghc 
import TcType         as Ghc (isClassPred)
import Type           as Ghc hiding (typeKind) 
import TyCoRep        as Ghc 
import Class          as Ghc
import Unique         as Ghc
import RdrName        as Ghc
import SrcLoc         as Ghc 
import Name           as Ghc hiding (varName) 


-- import TyCon          as Ghc 
-- import DataCon        as Ghc 

import TysPrim        as Ghc
import HscTypes       as Ghc
import HscMain        as Ghc 
import Id             as Ghc hiding (lazySetIdInfo, setIdExported, setIdNotExported) 

-- import qualified CoreSyn   as Ghc
-- import qualified Unique
-- import qualified GHC       as Ghc
-- import           Id
-- import           NameSet
-- -- import           Name
-- import           TyCon
-- import           Var
-- import           TysWiredIn
-- import           DataCon                                    (DataCon)
-- import           InstEnv
-- import           FamInstEnv
-- import           TcRnDriver (runTcInteractive)
-- import           FamInst    (tcGetFamInstEnvs)

