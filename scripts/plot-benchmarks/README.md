Plot-Benchmarks
===============

Overview
--------

Plot-Benchmarks is a tool designed to ingest a directory full of LiquidHaskell test suite logs and generate graphs of performance data over time.

Usage
-----

```
  -l --logdir=ITEM            The directory that contains the logs
  -o --outputdir=ITEM         The diretory to output graphs to
     --plotcompare=ITEM,ITEM  Pairs of benchmarks to compare
     --plot=ITEM              Benchmarks to plot
  -? --help                   Display help message
  -V --version                Print version information
     --numeric-version        Print just the version number
```

* `logdir`: The directory that contains log files to be considered. Defaults to the current directory (`./`).

* `outputdir`: The directory to write resulting graphs to. Defaults to the current directory (`./`).

* `plot`: A benchmark to plot. This is drawn from the first column of the LiquidHaskell log file and takes the form of `/intermediate/suite/container/TestFile.hs`. For each benchmark, one .svg file will be produced in the output directory.

* `plotcompare`: Two benchmarks to plot against each other. This is drawn from the first column of the LiquidHaskell log file and takes the form of `/intermediate/suite/container/TestFileLHS.hs,/some/other/suite/TestFileRHS.hs`. For each pair of benchmarks, one .svg file will be produced in the output directory.

Prerequisites
-------------

This program relies on a special header being present in the test suite output. This header is implemented in the master branch as of commit `29d72f62fd7f2d90574ad0d587185101ad960b23`. For any log file created prior to this commit, the following header can be prepended to the log file:

```
Epoch Timestamp: 1454554725
--------------------------------------------------------------------------------
```

This timestamp is required for plot-benchmarks to properly order each log. This time should be the *commiter* date of the git commit. An appropriate timestamp will be produced by git using the following command: `git show --format="%ct" --quiet`

Examples
--------

* `plot-benchmarks --plot Tests/Unit/pos/PointDist.hs --plotcompare Tests/Unit/pos/vector0.hs,Tests/Unit/neg/vector0.hs`

This will produce two .svg files in the current directory: one that plots the results of `Tests/Unit/pos/PointDist.hs`, and one that plots both `Tests/Unit/pos/vector0.hs` and `Tests/Unit/neg/vector0.hs`.

* `plot-benchmarks --logdir /tmp --plot Tests/Unit/pos/PointDist.hs --outputdir /tmp/results`

This will read log data from `/tmp` and create one .svg file for `Tests/Unit/pos/PointDist.hs` in `/tmp/results`
