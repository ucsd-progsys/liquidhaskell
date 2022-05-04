# Liquid Haskell Tests

## Directory Structure

- `./tests.cabal`: master cabal file for the tests, containing tests organized
  by group.
- `./harness/`: The test driver itself.
- `./app/Main.hs`: A dummy Main file shared between test group executables.
- `./benchmarks/`: benchmark-style tests, which are run for judging the
  performance of Liquid.
- `./errors/`: Tests for checking specific error messages. For the list of
  messages expected, see `./harness/Test/Groups.hs`.
- everything else in `./`: folders for different classes of tests, often
  containing `pos` and `neg` subfolders for positive and negative tests
  respectively.

## `test-driver` Executable

See the code for comments and documentation that is likely more up to date than
this file. The test driver parses the output of stack or cabal to summarize the
result of compiling specific test groups, represented in `tests.cabal` as
separate executables. The rest of this file describes how to modify the test
suite by adding new tests.

### Adding a Test

Adding a new test to an existing test group is straight-forward: create a new
file in the source directory specified in the cabal file for that test group (ie
the one that isn't `./app`). Add that file to the list of files under
`other-modules` in tests.cabal. If it is an error message test (ie part of the
`errors` test-group), add an error snippet to `./harness/Test/Groups.hs`
containing part of the error you want to be output by the test; see the examples
already present there.

If the test you wish to add has multiple files (ie one that imports others),
simply add each of the files to `other-modules`. Cabal and/or stack will figure
out the dependencies.

### Adding a Test Group

Adding a new test-group is also fairly simple: the easiest way is to just
copy-paste an existing test group, modify the source directories, other-modules,
flags, and dependencies as needed, create a new flag for the test group with the
same name, and ensure the guard clause.

```cabal
if !flag(<test-group-name>) && flag(stack):
  buildable: False
```

is present. This clause is a workaround for stack insisting on building every
executable in a cabal file once on first run, unless the executable is marked as
not buildable. Add a line in `./harness/Test/Groups.hs` corresponding
to the flavor (positive -> `TFSafe`, negative -> `TFUnsafe`, etc) and location
of the test.

Finally, ensure the test-group is runnable by doing `cabal v2-run
tests:test-driver -- <test-group-name>`.

### Adding a Benchmark

Adding a new benchmark is a little more involved: adapt the cabal file of the
benchmark and paste the relevant contents into `tests.cabal`. It is currently
not possible to use the native cabal file of the project directly without
hackery with the project files. See the examples already present in
`tests.cabal`. Note that benchmark test-group names start with `benchmark-` (eg
`benchmark-stitch-lh`) by convention. Again, ensure the benchmark has a guard
clause as in the above subsection. Test with `cabal v2-run tests:test-driver --
<benchmark-name>`.
