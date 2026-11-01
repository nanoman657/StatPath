# The HTTP client of http.bend against a local server: a GET of a file (200), a GET of a missing
# file (404, no body), and a POST whose body the server echoes (200). Run from the bend-tls
# directory: python3 -I e2e/http_test.py
import http.server
import os
import subprocess
import sys
import threading

PORT = 4480
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)

class Handler(http.server.BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.0"
    def log_message(self, *args):
        pass
    def do_GET(self):
        if self.path == "/crl.der":
            self.reply(200, b"CRLDER")
        else:
            self.reply(404, b"nope")
    def do_POST(self):
        n = int(self.headers.get("Content-Length", "0"))
        self.reply(200, self.rfile.read(n))
    def reply(self, status, body):
        self.send_response(status)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

def main():
    srv = http.server.ThreadingHTTPServer(("127.0.0.1", PORT), Handler)
    t = threading.Thread(target=srv.serve_forever, daemon=True)
    t.start()
    p = subprocess.run(["bend", "http_fetch.bend"], cwd=ROOT, capture_output=True, text=True, timeout=600)
    srv.shutdown()
    out = p.stdout + p.stderr
    want = ["get: body CRLDER", "missing: no body", "echo: body ping-body"]
    ok = p.returncode == 0 and all(line in out for line in want)
    for line in want:
        print(("PASS " if line in out else "FAIL ") + line)
    if not ok:
        print(out[-800:])
    print("http fetch: %d passed, %d failed" % (sum(l in out for l in want), len(want) - sum(l in out for l in want)))
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
