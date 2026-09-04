## Making a Liquid Haskell release

Here is a sequence of steps to make a release of Liquid Haskell.

### Make a release of Liquid Fixpoint

Make sure your liquid-fixpoint repository is up-to-date.

```
cd liquid-fixpoint
git fetch origin -p
git checkout origin/develop
```

Update the file `CHANGES.md`. There should be a log entry for each user facing change.
Usually the entries are possible to produce by inspecting the git history.
The following command gives the commits since the last release.

```
git log <tag_of_latest_release>..
```

Check that the version of `liquid-fixpoint` matches the earliest supported
compiler. Otherwise, adjust the version.
Now make sure that the latest version of liquidhaskell is still buildable
and all tests pass.

```
cd ..
git fetch origin -p
git checkout origin/develop
cabal test all
scripts/test/test_plugin.sh
```

Commit the changes and create a tag for the release

```
cd liquid-fixpoint
git add CHANGES.md liquid-fixpoint.cabal
git commit -m "Bump version of liquid-fixpoint to 0.9.6.3.6"
git tag v0.9.6.3.6
```

Upload the package to Hackage.

```
cabal sdist liquid-fixpoint
cabal upload --publish dist-newstyle/sdist/liquid-fixpoint-0.9.6.3.6.tar.gz
```

Hackage should be able to build the haddock documentation fine.

Push the changes to the github repo.

```
git push --tags origin HEAD:develop
```

### Make a release for Liquid Haskell

Make the `liquid-fixpoint` submodule point at the commit of the latest
release of Liquid Fixpoint.

The working copy of Liquid Haskell should already be up to date.

```
git checkout v0.9.6.3.6
cd ..
git add liquid-fixpoint
git commit -m "Update the liquid-fixpoint submodule"
```

Update the file `CHANGES.md` in a similar way to Liquid Fixpoint's.

Check the git history to see if new versions of other packages need to be
released (`liquid-vector`, `liquid-prelude`, `liquid-parallel`,
`liquid-finfield`).

The following command lists the commits to a given directory since the last
release.

```
git log <tag_of_latest_release>.. liquid-prelude
```

Check that the version of `liquidhaskell` and other packages match the
earliest supported compiler or library version. Otherwise, adjust the version.
Check that Liquid Haskell is buildable and that tests pass.

```
cabal build all
cabal test all
scripts/test/test_plugin.sh
```

Update installation instructions in the `docs/mkDocs/docs/install.md`.

Commit changes, and create a tag for the release

```
git add -up
git commit -m "Bump version of liquidhaskell to 0.9.14.1"
git tag v0.9.14.1
# create tags for other packages if released
git tag liquid-prelude-0.9.14.1
```

Upload the packages to Hackage.

```
cabal sdist liquidhaskell-boot
cabal sdist .
cabal upload --publish dist-newstyle/sdist/liquidhaskell-boot-0.9.14.1.tar.gz
# repeat for other packages if needed
```

Generate haddock documentation and upload it to Hackage.

```
cabal v2-haddock --haddock-for-hackage --enable-doc liquid-prelude
cabal upload -d --publish dist-newstyle/sdist/liquidhaskell-boot-0.9.14.1-docs.tar.gz
cabal upload -d --publish dist-newstyle/sdist/liquidhaskell-0.9.14.1-docs.tar.gz
# upload other packages if needed
```

Push the changes to the github repo.

```
git push --tags origin HEAD:develop
```

### Bump the version of Liquid Fixpoint and Liquid Haskell

Now bump the version of Liquid Fixpoint in the `liquid-fixpoint.cabal` file
to the next version. Then edit `liquidhaskell-boot.cabal` to allow the new
version of `liquid-fixpoint`. Bump the version of `liquidhaskell-boot` and
`liquidhaskell` as well. If there were releases of other packages, bump their
versions as well. Then make sure that the project builds without errors.

```
cabal build all
```

Push the changes to the github repo.

```
cd liquid-fixpoint
git add -up
git commit
git push origin HEAD:develop

cd ..
git add -up
git commit
git push origin HEAD:develop
```

### Update repositories that depend on releases

Update https://github.com/ucsd-progsys/lh-plugin-demo/

Update the version of Liquid Haskell used in https://ghc.gitlab.haskell.org/head.hackage/
