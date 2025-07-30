#!/usr/bin/env bash

# If calling with --make and no -no-link, then we are in the
# linking step of cabal and should remove from the command line
# -fforce-recomp -ddump-timings -ddump-to-file before calling ghc.
#
# This prevents ghc from recompiling the modules on linking and from
# overriding the timings in files.
if [ "$1" = "--make" ] && [ "$2" != "-no-link" ]; then
    # Remove -fforce-recomp, -ddump-timings, and -ddump-to-file from the arguments
    args=()
    for arg in "$@"; do
        if [[ "$arg" != "-fforce-recomp" && "$arg" != "-ddump-timings" && "$arg" != "-ddump-to-file" ]]; then
            args+=("$arg")
        fi
    done
else
    args=("$@")
fi

# Check if LIQUID_CABAL_PROJECT_FILE is set, otherwise print an error and exit.
if [ -z "$LIQUID_CABAL_PROJECT_FILE_GHC" ]; then
    echo "Error: LIQUID_CABAL_PROJECT_FILE_GHC is not set." >&2
    exit 1
fi

# Extract the ghc to use from the cabal.project file.
GHC=$(grep -E '^with-compiler:' "$LIQUID_CABAL_PROJECT_FILE_GHC" | awk '{print $2}' | head -n 1)
if [ -z "$GHC" ]; then
    GHC=ghc
fi

# remove the first entry from PATH so we invoke the real ghc binary
export PATH="${PATH#*tmp-measure-timings-bin:}"

# Call ghc with the remaining arguments
exec ${GHC} "${args[@]}"
