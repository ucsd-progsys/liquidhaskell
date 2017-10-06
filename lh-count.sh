#!/bin/sh

set -euo pipefail

function die() {
    echo ${@} && exit -1
}

function count() {
    sloccount ${@} 2>/dev/null | egrep -o 'haskell=[0-9]+' | egrep -o '[0-9]+'
}

([ ${#} -gt 0 ] && [ ${#} -lt 2 ]) || die "Usage: ${0} path-to-hs-file"
[ -r ${1} ] || die "Cannot read: ${1}"

code=$(count ${1})

TMPFILE=$(mktemp "/tmp/XXX.hs")
cp "${1}" "${TMPFILE}"
sed -i -e 's/{-@/{-# LH/g' "${TMPFILE}"
code_and_spec=$(count ${TMPFILE})

typesigs=$(./CountTypeSigs.hs "${1}")

echo "CODE: $((${code} - ${typesigs}))"
echo "SPEC: $(((${code_and_spec} - ${code} + ${typesigs})))"
echo "CODE + SPEC: ${code_and_spec}"
