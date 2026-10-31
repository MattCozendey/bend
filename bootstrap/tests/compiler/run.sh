#!/bin/bash
# run.sh WORK: tests of kind c of the compiler of step 1, which the laws of
# bootstrap/bend/src/compiler/spec.bend (no_wrong_result, no_other_failure,
# enough_memory) replace once they are proven.
# Each program of progs/ is compiled, and its module runs on each input in two
# real engines (W5): bun's JavaScriptCore and node's V8. Each must give the
# result that the Lean interpreter gives (scripts/Run.lean, which gives what
# Eval gives), or no result when it gives none. The compiler runs as the JS
# that `bend -o` writes for compile.bend; with TRUSTED=1, the Lean interpreter
# also runs it on progs/echo.bend, and must write the same bytes (this takes
# about an hour). Every tool is pinned: the script refuses to run with any
# other. WORK is a folder for what the tests write.
set -euo pipefail

BEND="bend 2.0.39"
BUN=1.4.4
NODE=v22.23.4

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
lean=$repo/bootstrap/lean
work=${1:?usage: run.sh WORK}
mkdir -p "$work"
work=$(cd "$work" && pwd)
export PATH=$HOME/.elan/bin:$PATH

bend() { bun "$repo/bend2/main.ts" "$@"; }
[ "$(bend version)" = "$BEND" ] || { echo "run.sh needs $BEND, not $(bend version)" >&2; exit 1; }
[ "$(bun --version)" = "$BUN" ] || { echo "run.sh needs bun $BUN, not $(bun --version)" >&2; exit 1; }
[ "$(node --version)" = "$NODE" ] || { echo "run.sh needs node $NODE, not $(node --version)" >&2; exit 1; }

# the inputs: a few texts, every byte, and pseudo-random bytes (a fixed LCG)
every=$work/every.in
printf "$(printf '\\%03o' $(seq 0 255))" > "$every"
random() { awk -v n="$1" 'BEGIN { x = 7; for (i = 0; i < n; i++) { x = (x * 1103515245 + 12345) % 2147483648; printf "%c", int(x / 65536) % 256 } }' LC_ALL=C; }
random 500 > "$work/random500.in"
head -c 20000 /dev/zero | tr '\0' 'x' > "$work/x20000.in"

declare -A inputs=(
  [echo]="text:hello,_world text: file:every"
  [rev]="text:hello text: file:every"
  [inc]="text:az file:every"
  [sort]="text:hello text:zyxwv file:random500"
  [count]="text: text:hello file:random500"
  [adder]="text:abc text:"
  [partial]="text:abc"
  [quant]="text:abc"
  [deep]="text:hello file:x20000"
  [big]="text:x"
  [rwt]="text:hello text:"
)

fails=0
bend "$here/compile.bend" -o "$work/compile.mjs" > /dev/null
for prog in "$here"/progs/*.bend; do
  n=$(basename "$prog" .bend)
  bend "$prog" -o "$work/$n.bendtt" > /dev/null
  (cd "$lean" && BOOK=$work/$n.bendtt OUTPUT=$work/$n.book lake lean scripts/Write.lean > /dev/null 2>&1)
  node "$here/compile.mjs" "$work/compile.mjs" "$work/$n.book" "$work/$n.wasm"
  for i in ${inputs[$n]}; do
    in=$work/$n.in
    case $i in
      text:*) printf '%s' "${i#text:}" | tr _ ' ' > "$in" ;;
      file:*) cp "$work/${i#file:}.in" "$in" ;;
    esac
    rm -f "$work/$n.want" "$work/$n.bun" "$work/$n.node"
    (cd "$lean" && BOOK=$work/$n.bendtt INPUT=$in OUTPUT=$work/$n.want lake lean scripts/Run.lean > /dev/null 2>&1) || true
    bun_says=$(bun "$here/host.mjs" "$work/$n.wasm" "$in" "$work/$n.bun" || true)
    node_says=$(node "$here/host.mjs" "$work/$n.wasm" "$in" "$work/$n.node" || true)
    if [ -f "$work/$n.want" ]; then
      if [ "$bun_says" = result ] && [ "$node_says" = result ] &&
        cmp -s "$work/$n.want" "$work/$n.bun" && cmp -s "$work/$n.want" "$work/$n.node"; then
        echo "ok   $n $i: the same $(wc -c < "$work/$n.want") bytes"
      else
        echo "FAIL $n $i: bun $bun_says, node $node_says, the interpreter a result"; fails=$((fails + 1))
      fi
    elif [ "$bun_says" != result ] && [ "$node_says" != result ]; then
      echo "ok   $n $i: no result (bun $bun_says, node $node_says)"
    else
      echo "FAIL $n $i: bun $bun_says, node $node_says, the interpreter no result"; fails=$((fails + 1))
    fi
  done
done

if [ -n "${TRUSTED:-}" ]; then
  bend "$here/compile.bend" -o "$work/compile.bendtt" > /dev/null
  (cd "$lean" && BOOK=$work/compile.bendtt INPUT=$work/echo.book OUTPUT=$work/echo.trusted.wasm FUEL=1000000000000 \
    lake lean scripts/Run.lean > /dev/null)
  if cmp -s "$work/echo.wasm" "$work/echo.trusted.wasm"; then
    echo "ok   the Lean interpreter compiles echo to the same bytes"
  else
    echo "FAIL the Lean interpreter compiles echo to other bytes"; fails=$((fails + 1))
  fi
fi

echo "$fails failed"
[ "$fails" = 0 ]
