# Writes client.bend from client_body.bend. Every socket reader is a chain of
# numbered stages, each calling only the next, so no IO function is recursive
# (Bend's checker takes no cycles through definitions):
#   io.rK      fill a buffer with at least `need` bytes (K stages)
#   f{k}       read the server's handshake records until its flight is complete
#   g{k}       read the server's application records until one does not open
#   python3 -I gen_client.py
K = 48   # fill stages: TCP reads per buffer fill
F = 24   # flight stages: server records read for the handshake flight
G = 24   # application stages: server records read for the response

def fill_stage(k):
    return f"""def io.r{k}.at(ok: Bool, s: Socket, +buf: List<&2, U32>, +need: Nat) -> IO(Socket & List<&2, U32>):
  match ok:
    case True{{}}:
      IO.pure(Socket & List<&2, U32>, (s, buf))
    case False{{}}:
      do IO<Socket & List<&2, U32>>:
        r : Socket & Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>> <- TCP.recv_bytes(s, 16384)
        io.r{k + 1}.got(r, buf, need)

def io.r{k + 1}.got(m: Socket & Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>>, +buf: List<&2, U32>,
  +need: Nat) -> IO(Socket & List<&2, U32>):
  (s, r) = m
  match r:
    case Fail{{(code, message)}}:
      IO.pure(Socket & List<&2, U32>, (s, buf))
    case Done{{None{{}}}}:
      IO.pure(Socket & List<&2, U32>, (s, buf))
    case Done{{Some{{+chunk}}}}:
      io.r{k + 1}.at(Nat.is_le(need, List.length(&2, U32, List.append(&2, U32, buf, chunk))), s,
        List.append(&2, U32, buf, chunk), need)
"""

fill = "".join(fill_stage(k) for k in range(K))
fill_entry = f"""
# bytes until buf holds need bytes (or the peer closes): the stage chain's entry
def io.fill(s: Socket, +buf: List<&2, U32>, +need: Nat) -> IO(Socket & List<&2, U32>):
  io.r0.at(Nat.is_le(need, List.length(&2, U32, buf)), s, buf, need)

# the fill chain ends at io.rK: a record that is still not whole after K reads is an error
def io.r{K}.at(ok: Bool, s: Socket, +buf: List<&2, U32>, +need: Nat) -> IO(Socket & List<&2, U32>):
  match ok:
    case True{{}}:
      IO.pure(Socket & List<&2, U32>, (s, buf))
    case False{{}}:
      do IO<Socket & List<&2, U32>>:
        Socket.close(s)
        IO.die(Socket & List<&2, U32>, 1, "a record was not complete after {K} reads")
"""

def record_chain(prefix, n, want, stop, strict=False):
    # stage k: at(done) returns when done, else reads one record and goes on;
    # the record's content joins the state when its content type is want
    out = []
    for k in range(n):
        out.append(f"""def {prefix}{k}.at(done: Bool, s: Socket, +st: Fl, +key: List<&2, U32>, +iv: List<&2, U32>) -> IO(Socket & Fl):
  match done:
    case True{{}}:
      IO.pure(Socket & Fl, (s, st))
    case False{{}}:
      do IO<Socket & Fl>:
        t : Socket & List<&2, U32> & List<&2, U32> <- io.record(s, fl.buf(st))
        {prefix}{k}.got(t, st, key, iv)

def {prefix}{k}.got(t: Socket & List<&2, U32> & List<&2, U32>, +st: Fl, +key: List<&2, U32>, +iv: List<&2, U32>) -> IO(Socket & Fl):
  (s, pr) = t
  (rest, rec) = pr
  {prefix}{k}.next(s, fl.next(st, rest, rec, key, iv, {want}), key, iv)

def {prefix}{k}.next(s: Socket, +st: Fl, +key: List<&2, U32>, +iv: List<&2, U32>) -> IO(Socket & Fl):
  {prefix}{k + 1}.at({stop(f"st")}, s, st, key, iv)

""")
    if strict:
        # the stream did not end within the stages: the response is longer than read
        out.append(f"""def {prefix}{n}.at(done: Bool, s: Socket, +st: Fl, +key: List<&2, U32>, +iv: List<&2, U32>) -> IO(Socket & Fl):
  match done:
    case True{{}}:
      IO.pure(Socket & Fl, (s, st))
    case False{{}}:
      do IO<Socket & Fl>:
        Socket.close(s)
        IO.die(Socket & Fl, 1, "the response is longer than the {n} records read: the stream was cut")

""")
    else:
        out.append(f"""def {prefix}{n}.at(+done: Bool, s: Socket, +st: Fl, +key: List<&2, U32>, +iv: List<&2, U32>) -> IO(Socket & Fl):
  IO.pure(Socket & Fl, (s, st))

""")
    return "".join(out)

flight = record_chain("f", F, "22", lambda st: f"flight.stop(fl.bad({st}), flight.done(fl.acc({st})))")
app = record_chain("g", G, "23", lambda st: f"fl.bad({st})", strict=True)

src = open("client_body.bend").read()
out = (src.replace("#@@STAGES@@", fill + fill_entry)
          .replace("#@@FLSTAGES@@", flight)
          .replace("#@@APPSTAGES@@", app))
open("client.bend", "w").write(out)
print("stages: fill", K, "flight", F, "app", G)
