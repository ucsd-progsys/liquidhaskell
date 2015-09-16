#!/bin/bash

SCRIPT_DIR=`pwd`;
GIPEDA_DIR="$SCRIPT_DIR/gipeda";
GIPEDA_SITE="$GIPEDA_DIR/site";

function abort_if_failed {
    local EXIT_CODE=$?;
    if [ $EXIT_CODE != 0 ]
    then
        echo $1;
        exit $EXIT_CODE;
    fi
}

./generate-logs.bash;
abort_if_failed "Failed to generate logs...";

cd $GIPEDA_DIR;
abort_if_failed "Unable to change to $GIPEDA_DIR..."; #You got problems

./gipeda;
abort_if_failed "Unable to generate report...";

echo "Site generation completed successfully!";
