#!/usr/bin/env bash
set -e

if [ -n "$LIQUID_CABAL_PROJECT_FILE" ]; then
    CABAL_BUILD_ARGS="--project-file=$LIQUID_CABAL_PROJECT_FILE"
fi

# used by ghc.sh to determine the cabal.project file to use.
export LIQUID_CABAL_PROJECT_FILE_GHC="$PWD/${LIQUID_CABAL_PROJECT_FILE:-cabal.project}"

# when --measure-timings is in the command line, setup the ghc wrapper
# to avoid overwriting the timings files. When linking, cabal-install
# passes to GHC -ddump-timings and -ddump-to-file, which causes GHC to
# overwrite the timings files.
if [[ "$@" == *"--measure-timings"* ]]; then
    # Extract the ghc to use from the cabal.project file.
    GHC=$(grep -E '^with-compiler:' "$LIQUID_CABAL_PROJECT_FILE_GHC" | awk '{print $2}' | head -n 1)
    if [ -z "$GHC" ]; then
        GHC=ghc
    fi

    echo creating tmp-measure-timings-bin directory ...
    # make directory for the temporary ghc wrapper
    TMPBIN="$PWD/tmp-measure-timings-bin"
    mkdir -p "$TMPBIN"
    # link the wrapper with the appropriate GHC name
    ln -f "$PWD/tests/harness/ghc.sh" "$TMPBIN/$GHC"
    chmod +x "$TMPBIN/$GHC"
    # put the temporary bin directory at the front of PATH
    export PATH="$TMPBIN:$PATH"
fi

set -x
# same as "cabal run tests:test-driver -- $@", but runs test-driver in the same
# environment as cabal, whereas "cabal run" does change the environment which
# then causes nested cabal calls to reconfigure packages.
cabal build $CABAL_BUILD_ARGS tests:test-driver
TEST_DRIVER=$(cabal exec -- bash -c "command -v test-driver")
"$TEST_DRIVER" $@
