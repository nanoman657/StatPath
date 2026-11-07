#!/bin/sh
# Regenerates layout.mjs from layout.bend with the installed bend (2.0.39 or later).
# The check runs first, so a module that does not check is never compiled.
set -eu
cd "$(dirname "$0")"
BEND_BIN="${BEND_BIN:-/root/.bend/bin/bend}"
"$BEND_BIN" layout.bend --check-only
"$BEND_BIN" layout.bend -o layout.mjs
