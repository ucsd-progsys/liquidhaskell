#!/bin/bash

SCRIPT_DIR=`dirname $0`;
SCRIPT_LOGS="$SCRIPT_DIR/logs";
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

echo "Deleting $SCRIPT_LOGS...";
rm -rf $SCRIPT_LOGS;
notify_if_failed "Failed to delete $SCRIPT_LOGS...";

if [ $FAILURES_OCCURRED = true ]
then
    echo "Cleanup failures occurred, please investigate...";
else
    echo "Cleanup completed successfully!";
fi
