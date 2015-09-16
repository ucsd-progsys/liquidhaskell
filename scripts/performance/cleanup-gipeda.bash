#!/bin/bash

SCRIPT_DIR=`pwd`;
GIPEDA_DIR="$SCRIPT_DIR/gipeda";
FAILURES_OCCURRED=false;

function notify_if_failed {
    local EXIT_CODE=$?;
    if [ $EXIT_CODE != 0 ]
    then
        echo $1;
        echo "Exit code was: $EXIT_CODE";
        $FAILURES_OCCURRED=true;
    fi
}

echo "Deleting $GIPEDA_DIR...";
rm -rf $GIPEDA_DIR;
notify_if_failed "Failed to delete $GIPEDA_DIR...";

if [ $FAILURES_OCCURRED = true ]
then
    echo "Cleanup failures occurred, please investigate...";
else
    echo "Cleanup completed successfully!";
fi
