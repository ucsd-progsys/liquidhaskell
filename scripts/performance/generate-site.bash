#!/bin/bash

GIT=`which git`;
CABAL=`which cabal`;
ALL_FOUND=true;

SCRIPT_DIR=`pwd`;
GIPEDA_DIR="$SCRIPT_DIR/gipeda";
GIPEDA_SITE="$GIPEDA_DIR/site";
GIPEDA_REPO="$GIPEDA_DIR/repository";
GIPEDA_LOGS="$GIPEDA_DIR/logs";

START=0
END=0
FORCE=0

function generate_log {
    local HASH=$1;
    local RETURN=0;

    # do stuff

    echo $RETURN;
}

function abort_if_failed {
    local EXIT_CODE=$?;
    if [ $EXIT_CODE != 0 ]
    then
        echo $1;
        exit $EXIT_CODE;
    fi
}

function usage {
    echo "$0 -s [START HASH] -e [END HASH] -f"
    echo "   -s - hash to start generating logs at";
    echo "   -e - hash to end generating logs at";
    echo "   -f - If passed, will force re-creation of all logs. Will take an extremely long time!";
    exit 1;
}

# Get options

while getopts ":s:e:f" OPT; do
    case $OPT in
        s)
            START=$OPTARG;;
        e)
            END=$OPTARG;;
        f)
            FORCE=1;;
        *)
            usage;;
    esac
done

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

if [ $ALL_FOUND = true ]
then
    echo "All dependencies met...";
else
    echo "Some dependencies are unmet...";
    exit 1;
fi

# generate logs

if [ ! -e $GIPEDA_LOGS ]
then
    mkdir $GIPEDA_LOGS;
    abort_if_failed "$GIPEDA_LOGS doesn't exist and couldn't be created...";
fi

cd $GIPEDA_REPO;
abort_if_failed "Couldn't change to $GIPEDA_REPO...";

for CURR in `git log --format=%H`
do
    RESULT=`generate_log $CURR`;
    if [ $RESULT = 0 ]
    then
        echo "Log generation for $CURR completed successfully...";
    else
        echo "Log generation for $CUR failed...";
    fi
done

# generate site

cd $GIPEDA_DIR;
abort_if_failed "Unable to change to $GIPEDA_DIR..."; #You got problems

./gipeda;
abort_if_failed "Unable to generate report...";

echo "Site generation completed successfully!";
