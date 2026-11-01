#!/bin/sh
# Builds the test-only BendTT kernel with an `eval` mode, for bendtt.test.ts.
#
#   BEND_DIR  the bend2 checkout whose bendtt.lean is patched (required). The patch was made against
#             bend2 at 9d514f3bb0d77524fcaa652645c902e4524eb838; another revision may not apply.
#   OUT       where to put the kernel (default: .build/bendtt-eval next to this script)
#   LEAN_BIN  the Lean 4.34.0 toolchain's bin directory (default: the one elan installs)
#
# The build is the one bend2's safe.ts uses (lean -c, then leanc -O3), on a patched copy of bendtt.lean,
# so the kernel's evaluator is the checked kernel's own, with only the `eval` mode added.
set -eu

here=$(cd "$(dirname "$0")" && pwd)
: "${BEND_DIR:?set BEND_DIR to the bend2 checkout (its bendtt.lean is patched)}"
OUT=${OUT:-$here/.build/bendtt-eval}
LEAN_BIN=${LEAN_BIN:-$HOME/.elan/toolchains/leanprover--lean4---v4.34.0/bin}
if [ -d "$LEAN_BIN" ]; then PATH="$LEAN_BIN:$PATH"; fi
export PATH

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cp "$BEND_DIR/bendtt.lean" "$tmp/bendtt.lean"
patch "$tmp/bendtt.lean" < "$here/bendtt-eval.patch" >/dev/null
cd "$tmp"
lean -c bendtt.c bendtt.lean
leanc -O3 -DNDEBUG bendtt.c -o bendtt
mkdir -p "$(dirname "$OUT")"
mv bendtt "$OUT"
echo "built $OUT"
