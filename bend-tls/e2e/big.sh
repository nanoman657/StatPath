#!/bin/bash
# Response size limits: a body of 200 KB (about 13 records) is printed in full, and
# one of 500 KB (more than the 24 records the client reads) must fail with the
# "stream was cut" error rather than print a partial page.
#   bash e2e/big.sh [native]
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(dirname "$HERE")
MODE=${1:-js}
PORT=${PORT:-4458}
WORK=$(mktemp -d)
SERVER=
cleanup() { [ -n "$SERVER" ] && kill "$SERVER" 2>/dev/null; rm -rf "$WORK"; }
trap cleanup EXIT

python3 -I "$HERE/mkpki.py" "$WORK" rsa >/dev/null || { echo "PKI generation failed"; exit 1; }
openssl x509 -in "$WORK/leaf.pem" -outform DER -out "$WORK/leaf.der" || exit 1
cat "$WORK/leaf.pem" "$WORK/inter.pem" > "$WORK/chain.pem"
cd "$ROOT" || exit 1
if [ "$MODE" = native ]; then
  timeout 580 bend client.bend -o "$WORK/client" >/dev/null 2>&1 || { echo "build failed"; exit 1; }
  RUN=("$WORK/client")
else
  RUN=(bend client.bend)
fi
pass=0; fail=0
run_size() {
  local size=$1
  python3 -I "$HERE/big_server.py" "$WORK/chain.pem" "$WORK/leaf.key" "$PORT" "$size" > "$WORK/server.log" 2>&1 &
  SERVER=$!
  sleep 1
  timeout 900 "${RUN[@]}" example.test 127.0.0.1 "$PORT" "$WORK/root.der" "$(date +%s)" > "$WORK/out.txt" 2>&1
  local code=$?
  kill "$SERVER" 2>/dev/null; wait "$SERVER" 2>/dev/null; SERVER=
  echo "$code" > "$WORK/code.txt"
}

run_size 200000
code=$(cat "$WORK/code.txt" 2>/dev/null || echo 1)
got=$(grep -o "A" "$WORK/out.txt" | wc -l)
if [ "$code" = 0 ] && [ "$got" -eq 200000 ]; then
  echo "PASS 200 KB body printed in full ($got bytes)"; pass=$((pass+1))
else
  echo "FAIL 200 KB body: exit $code, $got bytes of body"; tail -3 "$WORK/out.txt"; fail=$((fail+1))
fi
run_size 500000
code=$(cat "$WORK/code.txt" 2>/dev/null || echo 0)
if [ "$code" != 0 ] && grep -q "the stream was cut" "$WORK/out.txt"; then
  echo "PASS 500 KB body refused: the stream was cut"; pass=$((pass+1))
else
  echo "FAIL 500 KB body: exit $code, expected the cut-off error"; tail -3 "$WORK/out.txt"; fail=$((fail+1))
fi
echo "big ($MODE): $pass passed, $fail failed"
[ $fail -eq 0 ]
