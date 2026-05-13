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
OUT=$(cabal exec -- ghc -fplugin=LiquidHaskell $tmp_help_file 2> /dev/null)
[ $? -ne 0 ] || (echo "Expected non-zero exit code for --help" && exit 1)
echo $OUT | grep -q "Liquid Haskell Options" || echo "Help message not found" && exit 1

# Test that the help message is printed correctly
OUT=$(cabal exec -- ghc -fplugin=LiquidHaskell $tmp_version_file 2> /dev/null)
[ $? -ne 0 ] || (echo "Expected non-zero exit code for --version" && exit 1)
echo $OUT | grep -q "LiquidHaskell Version" || echo "Version message not found" && exit 1

echo "All tests passed!"
