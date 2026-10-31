#!/bin/bash
# convert.sh WORK: the binary scripts (wasm -d x.wast -o x.bin.wast) of the
# official WebAssembly tests that the Bend copy of WASM is tested with (W6),
# made by the spec's own reference interpreter. Every tool is pinned: the
# spec's commit, Ubuntu 24.04 and the exact packages below; the script
# refuses to run with anything else. WORK is a folder for the spec's clone
# and its build. The license, the tests (wast/) and their binary scripts
# (bin/) go next to this script.
set -euo pipefail

SPEC=https://github.com/WebAssembly/spec.git
COMMIT=6057acdb1a213f85369c64454c078a15f11ac4b1
PACKAGES=(ocaml=4.14.1-1ubuntu1 ocaml-dune=3.14.0-1 menhir=20231231+ds-1 libmenhir-ocaml-dev=20231231+ds-1)
TESTS=(binary binary-leb128 i32 int_exprs address align endianness load store memory memory_grow
  memory_size memory_trap data block loop br br_if br_table labels local_get local_set local_tee
  exports unreached-invalid)

here=$(cd "$(dirname "$0")" && pwd)
work=${1:?usage: convert.sh WORK}

. /etc/os-release
if [ "$ID $VERSION_ID" != "ubuntu 24.04" ]; then
  echo "convert.sh needs Ubuntu 24.04, not $ID $VERSION_ID" >&2
  exit 1
fi
for p in "${PACKAGES[@]}"; do
  have=$(dpkg-query -W -f='${Version}' "${p%%=*}" 2>/dev/null || true)
  if [ "$have" != "${p#*=}" ]; then
    echo "convert.sh needs ${p%%=*} ${p#*=}, not '${have:-none}': apt-get install ${PACKAGES[*]}" >&2
    exit 1
  fi
done

mkdir -p "$work"
cd "$work"
[ -d spec/.git ] || git init -q spec
cd spec
git fetch -q --depth 1 "$SPEC" "$COMMIT"
git checkout -q --detach FETCH_HEAD
if [ "$(git rev-parse HEAD)" != "$COMMIT" ]; then
  echo "convert.sh: the spec is not at $COMMIT" >&2
  exit 1
fi

make -C interpreter wasm
rm -rf "$here/wast" "$here/bin"
mkdir -p "$here/wast" "$here/bin"
cp test/LICENSE "$here/LICENSE"
for t in "${TESTS[@]}"; do
  cp "test/core/$t.wast" "$here/wast/$t.wast"
  interpreter/wasm -d "test/core/$t.wast" -o "$here/bin/$t.bin.wast"
done
