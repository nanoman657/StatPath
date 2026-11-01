#!/bin/bash
# End-to-end test: client.bend fetches GET / from `openssl s_server`, which speaks
# TLS 1.3 with TLS_CHACHA20_POLY1305_SHA256 over X25519 and an RSA certificate
# chain (leaf, intermediate) for example.test. The client is checked against the
# root as its trust anchor. Negative cases must fail the handshake.
#
#   bash e2e/run.sh            # JS (bend client.bend ...)
#   bash e2e/run.sh native     # native binary (bend client.bend -o ...)
#
# Needs openssl and Python's cryptography package. Regenerate client.bend first
# with gen_client.py if client_body.bend changed (see README).
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(dirname "$HERE")
MODE=${1:-js}
PORT=${PORT:-4433}
WORK=$(mktemp -d)
cleanup() { kill "$SERVER" 2>/dev/null; rm -rf "$WORK"; }

python3 -I "$HERE/mkpki.py" "$WORK" >/dev/null || { echo "PKI generation failed"; exit 1; }
openssl x509 -in "$WORK/leaf.pem" -outform DER -out "$WORK/leaf.der" || exit 1
openssl s_server -accept "$PORT" -cert "$WORK/leaf.pem" -cert_chain "$WORK/inter.pem" \
  -key "$WORK/leaf.key" -tls1_3 -ciphersuites TLS_CHACHA20_POLY1305_SHA256 -groups X25519 \
  -www > "$WORK/server.log" 2>&1 &
SERVER=$!
trap cleanup EXIT
sleep 1

cd "$ROOT" || exit 1
if [ "$MODE" = native ]; then
  timeout 580 bend client.bend -o "$WORK/client" >/dev/null 2>&1 || { echo "build failed"; exit 1; }
  RUN=("$WORK/client")
else
  RUN=(bend client.bend)
fi
NOW=$(date +%s)
pass=0; fail=0

# expect <name> <want: ok|fail> <host> <anchor> <time>
expect() {
  local name=$1 want=$2
  shift 2
  timeout 300 "${RUN[@]}" "$1" 127.0.0.1 "$PORT" "$2" "$3" > "$WORK/out.txt" 2>&1
  local code=$?
  if [ "$want" = ok ]; then
    if [ $code -eq 0 ] && grep -q "HTTP/1.0 200" "$WORK/out.txt"; then
      echo "PASS $name: fetched the page (HTTP/1.0 200)"; pass=$((pass+1))
    else
      echo "FAIL $name: exit $code"; grep -v '^$' "$WORK/out.txt" | tail -3; fail=$((fail+1))
    fi
  else
    if [ $code -ne 0 ] && grep -q "did not check" "$WORK/out.txt"; then
      echo "PASS $name: rejected, as it should be"; pass=$((pass+1))
    else
      echo "FAIL $name: exit $code, expected a rejected handshake"; grep -v '^$' "$WORK/out.txt" | tail -3; fail=$((fail+1))
    fi
  fi
}

expect valid ok example.test "$WORK/root.der" "$NOW"
expect wrong-anchor fail example.test "$WORK/leaf.der" "$NOW"
expect wrong-host fail other.test "$WORK/root.der" "$NOW"
expect expired fail example.test "$WORK/root.der" 4102444800
echo "e2e ($MODE): $pass passed, $fail failed"
[ $fail -eq 0 ]
