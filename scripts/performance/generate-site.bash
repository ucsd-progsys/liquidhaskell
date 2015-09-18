#!/bin/bash -x

GIT=`which git`;
MAKE=`which make`;
CABAL=`which cabal`;
ALL_FOUND=true;

SCRIPT_DIR=`pwd`;
GIPEDA_DIR="$SCRIPT_DIR/gipeda";
GIPEDA_SITE="$GIPEDA_DIR/site";
GIPEDA_REPO="$GIPEDA_DIR/repository";
GIPEDA_LOGS="$GIPEDA_DIR/logs";
REPO_TEST="$GIPEDA_REPO/dist/build/test/test";
REPO_LOG="$GIPEDA_REPO/tests/logs/cur/summary.csv";

START=0;
END=0;
FORCE=false;

START_FOUND=false;
END_FOUND=false;

function generate_log {
    local HASH=$1;
    local RETURN=0;
    local RESULT=$GIPEDA_LOGS/$HASH.log;
    local SHOULD_GEN=true;

    if [ -e $RESULT ]
    then
        if [ $FORCE = false ]
        then
            SHOULD_GEN=false;
        fi
    fi

    if [ $SHOULD_GEN = true ]
    then
        $GIT checkout $HASH
        $MAKE clean;
        if [ $? != 0 ]
        then
            return 1;
        fi

        rm -rf .cabal-sandbox;
        rm cabal.sandbox.config;

        $CABAL sandbox init;
        if [ $? != 0 ]
        then
            return 1;
        fi

        $CABAL install --enable-tests;
        if [ $? != 0 ]
        then
            return 1;
        fi

        $CABAL configure -fdevel --enable-tests --disable-library-profiling -O2;
        if [ $? != 0 ]
        then
            return 1;
        fi

        $CABAL build;
        if [ $? != 0 ]
        then
            return 1;
        fi

        $CABAL exec $REPO_TEST;
        if [ $? != 0 ]
        then
            return 1;
        fi

        cp $REPO_LOG $RESULT
        if [ $? != 0 ]
        then
            return 1;
        fi
    fi

    return 0;
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
    echo "   -f - If passed, will force re-creation of all logs. This will take an extremely long time!";
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
            FORCE=true;;
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

if [ $MAKE = "" ]
then
    echo "Make not found...";
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

if [ $START = 0 ]
then
    START_FOUND=true;
fi

for CURR in `$GIT show-ref --tags | grep liquidhaskell | cut -c -40`
do
    if [ $END_FOUND = false ]
    then
        if [ $START_FOUND = false ]
        then
            if [ $CURR = $START ]
            then
                START_FOUND=true;
            fi
        fi

        if [ $START_FOUND = true ]
        then
            echo "Processing: $CURR";
            generate_log $CURR;
        fi

        if [ ! $? = 0 ]
        then
            echo "Log generation for $CURR failed...";
        fi

        if [ $CURR = $END ]
        then
            END_FOUND=true;
        fi
    fi

done

# generate site

cd $GIPEDA_DIR;
abort_if_failed "Unable to change to $GIPEDA_DIR..."; #You got problems

exit 0;
# from here down is TODO

./gipeda;
abort_if_failed "Unable to generate report...";

echo "Site generation completed successfully!";
