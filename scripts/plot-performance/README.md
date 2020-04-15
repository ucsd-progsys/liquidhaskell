## Visualising performance of LH's testsuite

We offer a simple script to generate a gnuplot (under the form of a `.png` file) from `.csv` files
produced by LH's testuite. It will produce something like this:

![perf-min](https://user-images.githubusercontent.com/442035/78143687-e3f4a480-742e-11ea-9a47-6b1800914a15.png)

### Usage

In order to measure, say, regression between two LH branches, it's first necessary to acquire two `.csv`
files to compare. For example, suppose you want to measure the performance changes between `develop` and
a `new-feature` branch. The easiest way is to do something like this:

```
git checkout develop
stack build
stack test -j1 liquidhaskell:test --flag liquidhaskell:include --flag liquidhaskell:devel --test-arguments="-p Micro"
git checkout new-feature
stack build
stack test -j1 liquidhaskell:test --flag liquidhaskell:include --flag liquidhaskell:devel --test-arguments="-p Micro"
```

After doing so, inside `tests/logs` you will find a bunch of folders named after your hostname, with some
timestamps. At that point you can simply do:

```
./chart_perf.sh ../path/to/develop.csv ../path/to/new_feature.csv
```

The order is _chronological_, i.e. the first csv should be the "before" and the second the "after". After
you do that, you should hopefully have a `perf.png` image on your filesystem to inspect.
