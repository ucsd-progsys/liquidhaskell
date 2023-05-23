{-# LANGUAGE OverloadedStrings #-}

module Test.Groups where

import Data.Text (Text)

microTestGroups :: [Text]
microTestGroups =
  [ -- micros
    "unit-pos-1"
  , "unit-pos-2"
  , "unit-neg"
  , "basic-pos"
  , "basic-neg"
  , "class-pos"
  , "class-neg"
  , "parser-pos"
  , "measure-pos"
  , "measure-neg"
  , "datacon-pos"
  , "datacon-neg"
  , "names-pos"
  , "names-neg"
  , "reflect-pos"
  , "reflect-neg"
  , "absref-pos"
  , "absref-neg"
  , "import-cli"
  , "ple-pos"
  , "ple-neg"
  , "rankN-pos"
  , "terminate-pos"
  , "terminate-neg"
  , "pattern-pos"
  , "typeclass-pos"
  ]

benchmarkTestGroups :: [Text]
benchmarkTestGroups =
  [ -- benchmarks
    "benchmark-stitch-lh"
    -- XXX(matt.walker): I can't get this to work yet, but it mysteriously
    --                   works in the old test framework...
    -- , TestGroupData "benchmark-text" "benchmarks/text-0.11.2.3" TFBench
  , "benchmark-bytestring"
  , "benchmark-vector-algorithms"
  , "benchmark-cse230"
  , "benchmark-esop2013"
  , "benchmark-icfp15-pos"
  , "benchmark-icfp15-neg"
  ]

proverTestGroups :: [Text]
proverTestGroups =
  [ -- prover
    "prover-foundations"
    -- NOTE: This is compiled automatically as a dependency
    --, TestGroupData "prover-ple-lib" "benchmarks/popl18/lib" TFBench
  , "prover-ple-pos"
  , "prover-nople-pos"
  , "prover-nople-neg"
  ]

errorsTestGroups :: [Text]
errorsTestGroups =
  [ -- error messages
    "errors"
  , "parsing-errors"
  ]

relationalTestGroups :: [Text]
relationalTestGroups =
  [ "relational-pos"
  , "relational-neg"
  ]

-- | Update this when you add new "classes" of test groups
allTestGroupNames :: [Text]
allTestGroupNames =
  mconcat [ microTestGroups
          , benchmarkTestGroups
          , proverTestGroups
          , errorsTestGroups
          , relationalTestGroups
          ]
