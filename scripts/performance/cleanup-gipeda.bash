#!/bin/bash

SCRIPT_DIR=`pwd`;
GIPEDA_DIR="$SCRIPT_DIR/gipeda";

function notify_if_failed {
    local EXIT_CODE=$?;
    if [ $EXIT_CODE != 0 ]
    then
        echo $1;
        echo "Exit code was: $EXIT_CODE";
    fi
}

echo "Deleting $GIPEDA_DIR...";
rm -rf $GIPEDA_DIR;
notify_if_failed "Failed to delete $GIPEDA_DIR...";
