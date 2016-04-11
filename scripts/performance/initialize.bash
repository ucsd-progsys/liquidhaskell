#!/bin/bash

GIT=`which git`;
CABAL=`which cabal`;
GHC=`which ghc`;
ALL_FOUND=true;

SCRIPT_DIR=`dirname $0`;
SCRIPT_LOGS="$SCRIPT_DIR/logs";
SCRIPT_REPO="$SCRIPT_LOGS/repository";

LIQUID_URL="https://github.com/ucsd-progsys/liquidhaskell.git";

function abort_if_failed {
    local EXIT_CODE=$?;
    if [ $EXIT_CODE != 0 ]
    then
        echo $1;
        exit $EXIT_CODE;
    fi
}

# Check dependencies

if [ $GIT = "" ]
then
    echo "Git not found...";
    ALL_FOUND=false;
fi

if [ $CABAL = "" ]
then
    echo "Cabal not found...";
    ALL_FOUND=false;
else
    cabal sandbox --help &> /dev/null;
    if [ $? != 0 ]
    then
        echo "Cabal sandboxes not supported...";
        CABAL_VER=`cabal --numeric-version`;
        echo "Found Cabal version: $CABAL_VER, need 1.18 or greater..."
        ALL_FOUND=false;
    fi
fi

if [ $GHC = "" ]
then
    echo "GHC not found...";
    ALL_FOUND=false;
fi

if [ $ALL_FOUND = true ]
then
    echo "All dependencies met...";
else
    echo "Some dependencies are unmet...";
    exit 1;
fi

if [ -e $SCRIPT_LOGS ]
then
    echo "$SCRIPT_LOGS already exists, aborting..."
    exit 1;
fi

# clone repos

$GIT clone $LIQUID_URL $SCRIPT_REPO
abort_if_failed "Unable to clone Liquid Haskell...";

cd $SCRIPT_REPO;
abort_if_failed "Unable to change to $SCRIPT_REPO...";

$GIT submodule update --init;
abort_if_failed "Unable to initialize the git submodules...";

echo "Initialization completed successfully!";
