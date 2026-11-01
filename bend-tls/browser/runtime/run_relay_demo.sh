#!/bin/sh
# The relay demo: an echo server on 127.0.0.1:4444, the relay on ws://127.0.0.1:8766 allowing only
# that port, and relay_roundtrip.bend, which sends "hello" through the relay and prints the bytes
# that come back. It needs a Bend checkout with async-scheduler.patch applied, given as BEND_MAIN
# (the bend2/main.ts of that checkout). It prints "echoed 5".
#   BEND_MAIN=/path/to/bend/bend2/main.ts sh run_relay_demo.sh
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
bend=${BEND_MAIN:?"set BEND_MAIN to bend2/main.ts of a Bend checkout with async-scheduler.patch applied"}
tmp=$(mktemp -d)
trap 'kill $echo_pid $relay_pid 2>/dev/null; rm -rf "$tmp"' EXIT

cat > "$tmp/echo.py" <<'PY'
import socket
s = socket.socket()
s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
s.bind(("127.0.0.1", 4444))
s.listen(8)
while True:
    c, _ = s.accept()
    c.sendall(c.recv(65536))
    c.close()
PY
python3 -I "$tmp/echo.py" &
echo_pid=$!

echo '{"port":8766,"maxConnections":16,"allow":[{"host":"127.0.0.1","ports":[4444]}]}' > "$tmp/config.json"
(cd "$root/browser" && exec bun relay/relay.ts "$tmp/config.json") &
relay_pid=$!
sleep 1

cd "$here" && BEND_RELAY=ws://127.0.0.1:8766 timeout 60 bun "$bend" relay_roundtrip.bend
