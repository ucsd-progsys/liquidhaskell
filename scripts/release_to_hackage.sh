#!/usr/bin/env bash

set -euo pipefail

LIQUIDHASKELL_VER=$(cat "liquidhaskell.cabal" | grep "^version" | awk '{print $2}')
TO_UPLOAD=($(ls | grep "^liquid\-.*" | xargs echo))
GREEN='\033[0;32m'
NC='\033[0m' # no colour
UPLOAD_CMD=(cabal upload)
SDIST_CMD=(stack sdist)
TMP_TAR_DIR=$(mktemp -d /tmp/liquid-release.XXXXXX)
USER_PROVIDED_OPTIONS=$@

# Run the upload command to actually upload the packages.
function doUpload {

    ${SDIST_CMD[@]} . "--tar-dir=$TMP_TAR_DIR"
    ${UPLOAD_CMD[@]} ${USER_PROVIDED_OPTIONS[@]} "$TMP_TAR_DIR/liquidhaskell-$LIQUIDHASKELL_VER.tar.gz"

    for pkg in "${TO_UPLOAD[@]}"
    do
        pkg_version=$(cat $pkg/$pkg.cabal | grep "^version" | awk '{print $2}')
        ${SDIST_CMD[@]} $pkg "--tar-dir=$TMP_TAR_DIR"
        ${UPLOAD_CMD[@]} ${USER_PROVIDED_OPTIONS[@]} "$TMP_TAR_DIR/${pkg}-${pkg_version}.tar.gz"
    done
}

# Shows a recap of the packages that will be uploaded, as well as the commands that
# will be run.
function showRecap {

    echo -e "\nThe following packages will be uploaded:\n"

    echo -e liquidhaskell-${GREEN}$LIQUIDHASKELL_VER${NC}
    for pkg in "${TO_UPLOAD[@]}"
    do
        pkg_version=$(cat $pkg/$pkg.cabal | grep "^version" | awk '{print $2}')
        echo -e $pkg-${GREEN}$pkg_version${NC}
    done

    echo -e "\nHere is what I will run:\n"

    # Special treatment for liquidhaskell (due to the megarepo structure)
    echo "${SDIST_CMD[@]} . --tar-dir=$TMP_TAR_DIR"
    echo "${UPLOAD_CMD[@]} ${USER_PROVIDED_OPTIONS[@]} $TMP_TAR_DIR/liquidhaskell-$LIQUIDHASKELL_VER.tar.gz"

    echo ""

    for pkg in "${TO_UPLOAD[@]}"
    do
        pkg_version=$(cat $pkg/$pkg.cabal | grep "^version" | awk '{print $2}')
        echo "${SDIST_CMD[@]} $pkg --tar-dir=$TMP_TAR_DIR"
        echo "${UPLOAD_CMD[@]} ${USER_PROVIDED_OPTIONS[@]} $TMP_TAR_DIR/${pkg}-${pkg_version}.tar.gz"
        echo ""
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
