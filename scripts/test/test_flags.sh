#!/usr/bin/env bash

# This script tests that the --help and --version flags for Liquid Haskell print
# the text they are expected to print and terminate with non-zero exit code.

# Write a Haskell file that uses --help
tmp_help_file=$(mktemp --suffix=.hs)
cat <<EOF > "$tmp_help_file"
{-@ LIQUID "--help" @-}
main :: IO ()
main = putStrLn "Hello, Liquid Haskell!"
EOF

# Write a Haskell file that uses --version
tmp_version_file=$(mktemp --suffix=.hs)
cat <<EOF > "$tmp_version_file"
{-@ LIQUID "--version" @-}
main :: IO ()
main = putStrLn "Hello, Liquid Haskell!"
EOF
trap "rm -f $tmp_version_file $tmp_help_file" EXIT

# Test that the help message is printed correctly
OUT=$(cabal exec -- ghc -fplugin=LiquidHaskell $tmp_help_file 2>&1)
EXIT_CODE=$?
if [ $EXIT_CODE -eq 0 ]; then
  echo "ERROR: Expected non-zero exit code for --help, but got 0" >&2
  exit 1
fi
if ! echo "$OUT" | grep -q "Liquid Haskell Options"; then
  echo "ERROR: Help message not found in output" >&2
  echo "Got output:" >&2
  echo "$OUT" >&2
  exit 1
fi
echo LiquidHaskell --help: PASSED

# Test that the version message is printed correctly
OUT=$(cabal exec -- ghc -fplugin=LiquidHaskell $tmp_version_file 2>&1)
EXIT_CODE=$?
if [ $EXIT_CODE -eq 0 ]; then
  echo "ERROR: Expected non-zero exit code for --version, but got 0" >&2
  exit 1
fi
if ! echo "$OUT" | grep -q "LiquidHaskell Version"; then
  echo "ERROR: Version message not found in output" >&2
  echo "Got output:" >&2
  echo "$OUT" >&2
  exit 1
fi
echo LiquidHaskell --version: PASSED

echo "All tests passed!"
