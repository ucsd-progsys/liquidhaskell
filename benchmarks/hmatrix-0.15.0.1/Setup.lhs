#! /usr/bin/env runhaskell

> import Distribution.Simple
> import Distribution.Simple.Setup
> import Distribution.PackageDescription
> import Distribution.Simple.LocalBuildInfo

> import System.Process(system)
> import Config(config)

> main = defaultMainWithHooks simpleUserHooks { confHook = c }

> c x y = do
>     binfo <- confHook simpleUserHooks x y
>     pbi <- config binfo
>     let pkg_descr = localPkgDescr binfo
>     return $ binfo { localPkgDescr = updatePackageDescription pbi pkg_descr }

