#!/usr/bin/env bash
set -e

CABAL_BUILD_ARGS=$([ -n "$LIQUID_CABAL_PROJECT_FILE" ] && echo --project-file=$LIQUID_CABAL_PROJECT_FILE || true)

set -x
# same as "cabal run tests:test-driver -- $@", but runs test-driver in the same
# environment as cabal, whereas "cabal run" does change the environment which
# then causes nested cabal calls to reconfigure packages.
cabal build $CABAL_BUILD_ARGS tests:test-driver
TEST_DRIVER=$(cabal exec -- bash -c "command -v test-driver")
"$TEST_DRIVER" $@
