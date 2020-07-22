#!/usr/bin/env bash

TO_UPLOAD=($(ls | grep "^liquid\-.*" | xargs echo))
GREEN='\033[0;32m'
NC='\033[0m' # no colour
UPLOAD_CMD=(stack upload)

# Run the upload command to actually upload the packages.
function doUpload {
    for pkg in "${TO_UPLOAD[@]}"
    do
        ${UPLOAD_CMD[@]} $pkg
    done
}

# Shows a recap of the packages that will be uploaded, as well as the commands that
# will be run.
function showRecap {

    echo -e "\nThe following packages will be uploaded:\n"

    for pkg in "${TO_UPLOAD[@]}"
    do
        pkg_version=$(cat $pkg/$pkg.cabal | grep "^version" | awk '{print $2}')
        echo -e $pkg-${GREEN}$pkg_version${NC}
    done

    echo -e "\nHere is what I will run:\n"

    for pkg in "${TO_UPLOAD[@]}"
    do
        echo "${UPLOAD_CMD[@]} ${pkg}"
    done

    echo ""

}

# Shows the recap and ask the user for a choice.
function main {

    showRecap

    read -p "Continue [Y/n]? " choice
    case "$choice" in
      y|Y ) doUpload;;
      n|N ) echo "Operation aborted.";;
      * ) echo "Invalid choice.";;
    esac

}

# Main starts here.
main
