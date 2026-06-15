{-@ LIQUID "--reflection" @-}

{-# LANGUAGE GADTs #-}

module ReproUse where

import ReproDef

main :: IO ()
main = pure ()

{-@ contradictionThere :: Evidence -> {v:() | 0 /= 0} @-}
contradictionThere :: Evidence -> ()
contradictionThere (Refuter p contra) = contra p
