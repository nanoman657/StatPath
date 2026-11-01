# Writes tlsget.bend: the client's TLS 1.3 handshake on a new connection, for the revocation URLs
# that are https (a CRL, or an OCSP responder that takes a POST). It is client_body.bend, built by
# gen_client.py, with the revocation run cut out (a fetch does not fetch), the request sent as given
# (rv.file of the Rev record), and the reply returned as bytes instead of printed. The server name
# is checked against the certificate, and the chain must end at the trust anchor der, as for the
# client. tlsget.bend imports no other module of this project that imports it back, so client.bend
# can import it (Bend rejects cycles through definitions).
#   python3 -I gen_tlsget.py
import os
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_client  # noqa: E402

src = open("client_body.bend").read()


def rep(text, old, new, count=1):
    n = text.count(old)
    assert n == count, (n, old[:70])
    return text.replace(old, new)


def cut(text, start, end, inclusive=True):
    i = text.index(start)
    j = text.index(end) + (len(end) if inclusive else 0)
    return text[:i] + text[j:]


src = rep(src, "import ./http.bend as HTTP\n", "")
src = rep(src, "import ./revoc.bend as RV\n", "")
src = rep(src, "import ./tlsget.bend as TG\n", "")
# the revocation run (flight.revocation, the rv functions, the stages) is not in a fetch
src = cut(src, "# Revocation (rv.on)", "#@@REVSTAGES@@")
src = rep(src, "    flight.revocation(s, st, c_hs, mst, ch, sh, der, rev, now, host, alg)" if False else
          "      flight.revocation(s, st, c_hs, mst, ch, sh, der, rev, now, host, alg)",
          "      client.finish(s, st, c_hs, mst, ch, sh, host, alg, rev)")
src = rep(src, """def client.finish(s: Socket, +st: Fl, +c_hs: List<&2, U32>, +mst: List<&2, U32>,
  +ch: List<&2, U32>, +sh: List<&2, U32>, +host: List<&2, U32>, +alg: Nat) -> IO(Unit):""",
          """def client.finish(s: Socket, +st: Fl, +c_hs: List<&2, U32>, +mst: List<&2, U32>,
  +ch: List<&2, U32>, +sh: List<&2, U32>, +host: List<&2, U32>, +alg: Nat, +rev: Rev) -> IO(Unit):""")
# the request is the Rev's bytes (the caller built it); the chain has no CRL to check
src = rep(src, "client.req(host)", "rv.file(rev)")
src = rep(src, "CR.crl.chain.ok(chain, der, rv.file(rev), now)", "CR.crl.chain.ok(chain, der, Nil{}, now)")
src = rep(src, "def io.fail(s: Socket, msg: String) -> IO(Unit):\n  do IO<Unit>:\n    Socket.close(s)\n    IO.die(Unit, 1, msg)\n\n", "")
src = src.replace("io.fail(", "tg.fail(")
# the reply is returned, not printed
src = rep(src, """def app.print(s: Socket, +st: Fl) -> IO(Unit):
  do IO<Unit>:
    Socket.close(s)
    IO.print(utf8(fl.acc(st)))
""", """def app.print(s: Socket, +st: Fl) -> IO(Maybe<&2, List<&2, U32>>):
  do IO<Maybe<&2, List<&2, U32>>>:
    Socket.close(s)
    IO.pure(Maybe<&2, List<&2, U32>>, Some{fl.acc(st)})
""")
# the client's entry point (run, start, main) is replaced by tg.get
src = cut(src, "# Main\n# ----", "# UTF-8 decoding", inclusive=False)
src = src.replace("-> IO(Unit):", "-> IO(Maybe<&2, List<&2, U32>>):")
src = src.replace("do IO<Unit>:", "do IO<Maybe<&2, List<&2, U32>>>:")

TG = '''# The TLS fetch: the client's handshake on a new connection, for a revocation URL. The request is
# req (the whole HTTP request, its Host header included); name is the server name, which the
# certificate must match; der is the trust anchor, which the chain must reach. The reply is the bytes
# the server sent, or None when the connection is refused or the handshake fails.
def tg.get(addr: String, port: Nat, +req: List<&2, U32>, +name: List<&2, U32>, +der: List<&2, U32>,
  now: Nat) -> IO(Maybe<&2, List<&2, U32>>):
  do IO<Maybe<&2, List<&2, U32>>>:
    c : Result<&1, &1, U32 & String, Socket> <- TCP.connect(addr, U32.from_nat(port))
    tg.opened(c, req, name, der, now)

def tg.opened(c: Result<&1, &1, U32 & String, Socket>, +req: List<&2, U32>, +name: List<&2, U32>,
  +der: List<&2, U32>, now: Nat) -> IO(Maybe<&2, List<&2, U32>>):
  match c:
    case Fail{(code, message)}:
      IO.pure(Maybe<&2, List<&2, U32>>, None{})
    case Done{sock}:
      tg.hello(sock, req, name, der, now)

def tg.hello(sock: Socket, +req: List<&2, U32>, +name: List<&2, U32>, +der: List<&2, U32>,
  now: Nat) -> IO(Maybe<&2, List<&2, U32>>):
  do IO<Maybe<&2, List<&2, U32>>>:
    +priv : List<&2, U32> <- io.rand(8n)
    +privr : List<&2, U32> <- io.rand(8n)
    +privq : List<&2, U32> <- io.rand(12n)
    +privs : List<&2, U32> = List.append(&2, U32, P.p256.scalar(privr), Q.p384.scalar(privq))
    +rnd : List<&2, U32> <- io.rand(8n)
    +ch : List<&2, U32> = hello.msg(priv, privs, rnd, name)
    s1 : Socket <- io.send(sock, T.tls.plain(22, ch))
    t : Socket & List<&2, U32> & List<&2, U32> <- io.record(s1, Nil{})
    hello.got(t, priv, privs, ch, der, Rev{req, False{}, Nil{}}, now, name)

# a failed step: the connection is closed, and the reply is None
def tg.fail(s: Socket, msg: String) -> IO(Maybe<&2, List<&2, U32>>):
  do IO<Maybe<&2, List<&2, U32>>>:
    Socket.close(s)
    IO.pure(Maybe<&2, List<&2, U32>>, None{})

'''
src = rep(src, "# UTF-8 decoding", TG + "# UTF-8 decoding")
out = "# tlsget.bend: the client's TLS 1.3 handshake for the https revocation URLs. Generated by\n" \
      "# gen_tlsget.py from client_body.bend (with gen_client.py's stages): do not edit it.\n\n" + gen_client.build(src)
open("tlsget.bend", "w").write(out)
print("tlsget.bend written")
