#!/bin/sh
# Regenerates merge.mjs from merge.bend with the installed bend (2.0.39 or later).
# The check runs first, so a module that does not check is never compiled.
set -eu
cd "$(dirname "$0")"
bend merge.bend --check-only
bend merge.bend -o merge.mjs
