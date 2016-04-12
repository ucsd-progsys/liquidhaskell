#!/bin/bash

GIT=`which git`;
MAKE=`which make`;
CABAL=`which cabal`;
ALL_FOUND=true;

SCRIPT_DIR=`dirname $0`;

SCRIPT_LOGS="$SCRIPT_DIR/logs";
SCRIPT_REPO="$SCRIPT_LOGS/repository";
SCRIPT_FIXPOINT="$SCRIPT_REPO/liquid-fixpoint";
SCRIPT_PROVER="$SCRIPT_REPO/prover";
REPO_TEST="$SCRIPT_REPO/dist/build/test/test";
REPO_TEST_ARGS=" --timeout 10m";
REPO_LOG="$SCRIPT_REPO/tests/logs/cur/summary.csv";

ALL_GIT_TAGS="$GIT show-ref --tags | grep liquidhaskell | cut -c -40";
ALL_GIT_HASHES="$GIT log --format=%H";

START=0;
END=0;
FORCE=false;
MAX_LOGS=-1;
DONE_LOGS=0;

START_FOUND=false;
END_FOUND=false;

function refresh_repo {
    cd $SCRIPT_REPO;
    abort_if_failed "Couldn't change to $SCRIPT_REPO...";

    $GIT pull origin master;

    if [ $END != 0 ]
    then
        $GIT checkout master;
        $GIT submodule update;
    fi

    abort_if_failed "Couldn't pull Liquid Haskell from remote...";

    $GIT reset;
    abort_if_failed "Couldn't reset the the liquid-haskell repository...";

    $GIT checkout .;
    abort_if_failed "Couldn't discard changes to liquid-haskell...";

    $GIT submodule foreach 'git reset ; git checkout . ;';
    abort_if_failed "Couldn't reset and discard changes to submodules...";
}

function generate_log {
    local HASH=$1;
    local RESULT=$SCRIPT_LOGS/$HASH.csv;
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
        DONE_LOGS=`expr $DONE_LOGS + 1`
        $GIT checkout $HASH;
        $GIT submodule update;
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

        $CABAL sandbox add-source $SCRIPT_FIXPOINT;
        $CABAL sandbox add-source $SCRIPT_PROVER;

        $CABAL install --enable-tests;
        if [ $? != 0 ]
        then
            return 1;
        fi

        $CABAL configure --enable-tests --disable-library-profiling -O2;
        if [ $? != 0 ]
        then
            return 1;
        fi

        $CABAL build;
        if [ $? != 0 ]
        then
            return 1;
        fi

        $CABAL exec $REPO_TEST -- $REPO_TEST_ARGS;
        # Not testing for failure; failed tests shouldn't prevent the site from
        # being generated.

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
    echo "$0 -s [START HASH] -e [END HASH] -f -n [MAX LOGS TO GENERATE]"
    echo "   -s - hash to start generating logs at";
    echo "   -e - hash to end generating logs at";
    echo "   -f - If passed, will force re-creation of all logs. This will take an extremely long time!";
    echo "   -n - Only generate n logs (useful for cron jobs and such)"
    exit 1;
}

# Get options

while getopts ":s:e:n:f" OPT; do
    case $OPT in
        s)
            START=$OPTARG;;
        e)
            END=$OPTARG;;
        f)
            FORCE=true;;
        n)
            MAX_LOGS=$OPTARG;;
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

$CABAL update;
abort_if_failed "Couldn't perform cabal update...";

# generate logs

if [ ! -e $SCRIPT_LOGS ]
then
    mkdir $SCRIPT_LOGS;
    abort_if_failed "$SCRIPT_LOGS doesn't exist and couldn't be created...";
fi

# Refresh the repo prior to working
refresh_repo;

if [ $END = 0 ]
then
    END_FOUND=true;
fi

for CURR in `$ALL_GIT_HASHES`
do
    if [ $START_FOUND = false ]
    then
        if [ $END_FOUND = false ]
        then
            if [ $CURR = $END ]
            then
                END_FOUND=true;
            fi
        fi

        if [ $END_FOUND = true ]
        then
            echo "Processing: $CURR";
            generate_log $CURR;
        fi

        if [ ! $? = 0 ]
        then
            echo "Log generation for $CURR failed...";
        fi

        if [ $CURR = $START ]
        then
            START_FOUND=true;
        fi

        if [ $MAX_LOGS = $DONE_LOGS  ]
        then
            START_FOUND=true;
        fi

        rm -rf /tmp/ghc*;
        rm -rf /tmp/cabal*;
    fi

done
