#!/bin/bash
# End-to-end test: client.bend fetches GET / from `openssl s_server`, which speaks
# TLS 1.3 over X25519 with a certificate chain (leaf, intermediate) for
# example.test. Each PKI kind (rsa, ec, mixed: see mkpki.py) and each cipher suite
# the client offers is tested on its own server. The client is checked against the
# root as its trust anchor. Negative cases must fail the handshake.
#
#   bash e2e/run.sh            # JS (bend client.bend ...)
#   bash e2e/run.sh native     # native binary (bend client.bend -o ...)
#
# Needs openssl and Python's cryptography package. Regenerate client.bend first
# with gen_client.py and sortfile.py if client_body.bend changed (see README).
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(dirname "$HERE")
MODE=${1:-js}
PORT=${PORT:-4433}
SUITES=${SUITES:-"TLS_CHACHA20_POLY1305_SHA256 TLS_AES_128_GCM_SHA256"}
PKIS=${PKIS:-"rsa ec mixed ed"}
KEX_GROUPS=${KEX_GROUPS:-"X25519 P-256"}
WORK=$(mktemp -d)
SERVER=

cleanup() { [ -n "$SERVER" ] && kill "$SERVER" 2>/dev/null; rm -rf "$WORK"; }
trap cleanup EXIT

cd "$ROOT" || exit 1
if [ "$MODE" = native ]; then
  timeout 580 bend client.bend -o "$WORK/client" >/dev/null 2>&1 || { echo "build failed"; exit 1; }
  RUN=("$WORK/client")
else
  RUN=(bend client.bend)
fi
NOW=$(date +%s)
pass=0; fail=0

# expect <label> <want: ok|fail> <host> <anchor> <time>
expect() {
  local label=$1 want=$2
  shift 2
  timeout 300 "${RUN[@]}" "$1" 127.0.0.1 "$PORT" "$2" "$3" > "$WORK/out.txt" 2>&1
  local code=$?
  if [ "$want" = ok ]; then
    if [ $code -eq 0 ] && grep -q "HTTP/1.0 200" "$WORK/out.txt"; then
      echo "PASS $label: fetched the page (HTTP/1.0 200)"; pass=$((pass+1))
    else
      echo "FAIL $label: exit $code"; grep -v '^$' "$WORK/out.txt" | tail -3; fail=$((fail+1))
    fi
  else
    if [ $code -ne 0 ] && grep -q "did not check" "$WORK/out.txt"; then
      echo "PASS $label: rejected, as it should be"; pass=$((pass+1))
    else
      echo "FAIL $label: exit $code, expected a rejected handshake"; grep -v '^$' "$WORK/out.txt" | tail -3; fail=$((fail+1))
    fi
  fi
}

for kind in $PKIS; do
  PKI="$WORK/pki-$kind"
  mkdir -p "$PKI"
  python3 -I "$HERE/mkpki.py" "$PKI" "$kind" >/dev/null || { echo "PKI generation failed ($kind)"; exit 1; }
  openssl x509 -in "$PKI/leaf.pem" -outform DER -out "$PKI/leaf.der" || exit 1
  for suite in $SUITES; do for group in $KEX_GROUPS; do
    openssl s_server -accept "$PORT" -cert "$PKI/leaf.pem" -cert_chain "$PKI/inter.pem" \
      -key "$PKI/leaf.key" -tls1_3 -ciphersuites "$suite" -groups "$group" \
      -www > "$PKI/server.log" 2>&1 &
    SERVER=$!
    sleep 1
    label="$kind/$suite/$group"
    expect "$label valid" ok example.test "$PKI/root.der" "$NOW"
    expect "$label wrong-anchor" fail example.test "$PKI/leaf.der" "$NOW"
    expect "$label wrong-host" fail other.test "$PKI/root.der" "$NOW"
    expect "$label expired" fail example.test "$PKI/root.der" 4102444800
    kill "$SERVER" 2>/dev/null; wait "$SERVER" 2>/dev/null; SERVER=
    sleep 1
  done; done
done
echo "e2e ($MODE): $pass passed, $fail failed"
[ $fail -eq 0 ]
