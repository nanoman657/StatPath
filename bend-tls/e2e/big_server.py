# A TLS 1.3 server for e2e/big.sh: it answers any request with a body of the given size.
#   python3 -I e2e/big_server.py <chain.pem> <key.pem> <port> <body bytes>
# The suite and group are whatever the client offers first (its own order decides).
import socket
import ssl
import sys

cert, key, port, size = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
ctx.minimum_version = ssl.TLSVersion.TLSv1_3
ctx.maximum_version = ssl.TLSVersion.TLSv1_3
ctx.load_cert_chain(cert, key)
body = b"A" * size
srv = socket.socket()
srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
srv.bind(("127.0.0.1", port))
srv.listen(5)
print("ready", flush=True)
while True:
    raw, _ = srv.accept()
    try:
        conn = ctx.wrap_socket(raw, server_side=True)
        conn.recv(4096)
        conn.sendall(b"HTTP/1.1 200 OK\r\nContent-Length: %d\r\nConnection: close\r\n\r\n" % len(body) + body)
        conn.unwrap()
    except Exception as e:  # the client may hang up early
        print("server:", e, flush=True)
    finally:
        raw.close()
