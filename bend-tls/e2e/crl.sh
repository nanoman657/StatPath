#!/usr/bin/env bash
# End-to-end test of the revocation check: client.bend is given a CRL with its trust anchor.
# A CRL that lists nothing lets the handshake through; a CRL signed by the intermediate that
# lists the server's leaf refuses it; without a CRL the handshake goes through as before.
#   bash e2e/crl.sh            # JS (bend client.bend ...)
#   bash e2e/crl.sh native     # native binary
# Needs openssl and Python's cryptography package.
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/.." && pwd)
PORT=${PORT:-4437}
MODE=${1:-js}
PKIS=${PKIS:-"rsa ec mixed ed ec384"}
SUITE=${SUITE:-TLS_AES_128_GCM_SHA256}
GROUP=${GROUP:-X25519}
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

# expect <label> <want: ok|fail> <crl or -> : the anchor is the root, the host example.test
expect() {
  local label=$1 want=$2 crl=$3 pki=$4
  local args=("${RUN[@]}" example.test 127.0.0.1 "$PORT" "$pki/root.der" "$NOW")
  [ "$crl" != "-" ] && args+=("$crl")
  timeout 300 "${args[@]}" > "$WORK/out.txt" 2>&1
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
  openssl s_server -accept "$PORT" -cert "$PKI/leaf.pem" -cert_chain "$PKI/inter.pem" \
    -key "$PKI/leaf.key" -tls1_3 -ciphersuites "$SUITE" -groups "$GROUP" \
    -www > "$PKI/server.log" 2>&1 &
  SERVER=$!
  sleep 1
  label="$kind"
  expect "$label no-crl" ok - "$PKI"
  expect "$label clean-crl" ok "$PKI/crl-clean.der" "$PKI"
  expect "$label revoked-leaf" fail "$PKI/crl-revoked.der" "$PKI"
  kill "$SERVER" 2>/dev/null; wait "$SERVER" 2>/dev/null; SERVER=
  sleep 1
done
echo "e2e crl ($MODE): $pass passed, $fail failed"
[ $fail -eq 0 ]
