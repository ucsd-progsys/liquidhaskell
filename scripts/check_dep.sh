#!/usr/bin/env sh
set -e

GHC_EXPECTED_VERSION="9.14.1"
CABAL_EXPECTED_VERSION="3.16.1.0"

SHOULD_INSTALL_DEPS=false

while [ $# -gt 0 ]; do
  case "$1" in
    --install-deps)
      SHOULD_INSTALL_DEPS=true
      shift
      ;;
    --help)
      echo "Usage: $0 [options]"
      echo "  --help"
      echo "  --install-deps"
      exit 0
      ;;
    *)
      echo "Unknown option: $1"
      exit 1
      ;;
  esac
done

check_ghcup() {
  if command -v ghcup >/dev/null 2>&1; then
    return 0
  fi
  echo "ghcup is not installed."

  echo "Installing ghcup..."
  case "$(uname -s)" in
    Linux|Darwin) ;;
    *) echo "Unsuppored platform"; exit 1 ;;
  esac

  curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
}

check_ghc() {
  if command -v ghc >/dev/null 2>&1; then
    GHC_VERSION="$(ghc --numeric-version)"
    if [ "$GHC_VERSION" = "$GHC_EXPECTED_VERSION" ]; then
        return 0
    fi
    echo "Expected ghc version $GHC_EXPECTED_VERSION, but found $GHC_VERSION."
  else
    echo "ghc is not installed."
  fi

  if [ "$SHOULD_INSTALL_DEPS" = false ]; then
    echo "Please install ghc version $GHC_EXPECTED_VERSION and try again."
    exit 1
  fi

  echo "Installing ghc version $GHC_EXPECTED_VERSION..."
  ghcup install ghc "$GHC_EXPECTED_VERSION"
  ghcup set ghc "$GHC_EXPECTED_VERSION"
  echo "Installed ghc version $GHC_EXPECTED_VERSION."
}

check_cabal() {
  if command -v cabal >/dev/null 2>&1; then
    CABAL_VERSION="$(cabal --numeric-version)"
    if [ "$CABAL_VERSION" = "$CABAL_EXPECTED_VERSION" ]; then
        return 0
    fi
    echo "Expected cabal version $CABAL_EXPECTED_VERSION, but found $CABAL_VERSION."
  else
    echo "cabal is not installed."
  fi

  if [ "$SHOULD_INSTALL_DEPS" = false ]; then
    echo "Please install cabal version $CABAL_EXPECTED_VERSION and try again."
    exit 1
  fi

  echo "Installing cabal version $CABAL_EXPECTED_VERSION..."
  ghcup install cabal "$CABAL_EXPECTED_VERSION"
  ghcup set cabal "$CABAL_EXPECTED_VERSION"
  echo "Installed cabal version $CABAL_EXPECTED_VERSION."
}

check_z3() {
  if command -v z3 >/dev/null 2>&1; then
    return 0
  fi
  echo "z3 is not installed."
  if [ "$SHOULD_INSTALL_DEPS" = false ]; then
    echo "Please install z3 and try again."
    exit 1
  fi
  echo "Installing z3 automatically is currently not supported."
}

if [ "$SHOULD_INSTALL_DEPS" = true ]; then
  check_ghcup
fi
check_ghc
check_cabal
check_z3
