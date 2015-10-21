#!/bin/bash

GIT=`which git`;
CABAL=`which cabal`;
GHC=`which ghc`;
ALL_FOUND=true;

SCRIPT_DIR=`dirname $0`;
GIPEDA_DIR="$SCRIPT_DIR/gipeda";
GIPEDA_REPO="$GIPEDA_DIR/repository";
REL_SANDBOX_BIN=".cabal-sandbox/bin";

GIPEDA_URL="https://github.com/nomeata/gipeda.git";
LIQUID_URL="https://github.com/ucsd-progsys/liquidhaskell.git";

SETTINGS_FILE="settings.yaml";
LOG2CSV="log2csv.hs";

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

if [ -e $GIPEDA_DIR ]
then
    echo "$GIPEDA_DIR already exists, aborting..."
    exit 1;
fi

# clone repos

mkdir $GIPEDA_DIR;
abort_if_failed "Unable to create $GIPEDA_DIR...";

$GIT clone $GIPEDA_URL $GIPEDA_DIR;
abort_if_failed "Unable to clone Gipeda...";

$GIT clone $LIQUID_URL $GIPEDA_REPO
abort_if_failed "Unable to clone Liquid Haskell...";

cd $GIPEDA_REPO;
abort_if_failed "Unable to change to $GIPEDA_REPO...";

$GIT submodule update --init;
abort_if_failed "Unable to initialize the Liquid-Fixpoint git submodule...";

# build gipeda in a sandbox, link executables

cd $GIPEDA_DIR;
abort_if_failed "Unable to change to $GIPEDA_DIR..."; #You got problems

$CABAL sandbox init;
abort_if_failed "Unable to initialize Cabal sandbox for Gipeda...";

$CABAL update;
abort_if_failed "Unable to perform cabal update...";

$CABAL install;
abort_if_failed "Unable to install Gipeda...";

ln -s $REL_SANDBOX_BIN/gipeda gipeda;
abort_if_failed "Unable to create link to Gipeda...";

# add settings.yaml and log2csv

cp $SCRIPT_DIR/$SETTINGS_FILE $GIPEDA_DIR;
abort_if_failed "Unable to install setttings.yaml...";

cp $SCRIPT_DIR/$LOG2CSV $GIPEDA_DIR;
abort_if_failed "Failed to copy $LOG2CSV to $GIPEDA_DIR...";

$CABAL exec $GHC -- $LOG2CSV -o $GIPEDA_DIR/log2csv
abort_if_failed "Unable to install log2csv...";

# install javascript libraries

./install-jslibs.sh
abort_if_failed "Unable to install javascript dependencies...";

echo "Deploy completed successfully!";
