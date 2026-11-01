#!/bin/sh
# Makes a checkout of the Bend toolchain (bendlang/bend) with the browser runtime patch applied,
# and prints the path of its main.ts. That path is BEND_MAIN for the browser tests and page builds.
#
#   sh patches/bend/apply.sh <dir>
#   BEND_MAIN=<dir>/bend2/main.ts bun test browser/test
#
# The patch is made on the base commit below. Running this twice is safe: the second run only
# switches to the branch the first made.
set -eu
BASE=9d514f3bb0d77524fcaa652645c902e4524eb838
REPO=https://github.com/bendlang/bend
dir=${1:?usage: apply.sh <dir>}
here=$(cd "$(dirname "$0")" && pwd)
if [ ! -d "$dir/.git" ]; then
  git clone -q --filter=blob:none --no-checkout "$REPO" "$dir"
fi
if git -C "$dir" rev-parse -q --verify refs/heads/browser-async-scheduler >/dev/null; then
  git -C "$dir" checkout -q browser-async-scheduler
else
  git -C "$dir" checkout -q -b browser-async-scheduler "$BASE"
  git -C "$dir" am -q "$here"/0001-*.patch
fi
echo "$dir/bend2/main.ts"
