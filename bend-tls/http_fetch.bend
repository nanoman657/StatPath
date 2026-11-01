# http_fetch.bend: three requests to a local server (e2e/http_test.py serves them on port 4480).
import Base
import ./http.bend as H

def show_reply(m: Maybe<&2, List<&2, U32>>) -> String:
  match m:
    case Some{+body}:
      "body " ++ H.http.ip_str(body)
    case None{}:
      "no body"

def main() -> IO(Unit):
  do IO<Unit>:
    get : Maybe<&2, List<&2, U32>> <- H.http.get_url("http://127.0.0.1:4480/crl.der")
    IO.print("get: " ++ show_reply(get) ++ "\n")
    missing : Maybe<&2, List<&2, U32>> <- H.http.get_url("http://127.0.0.1:4480/missing")
    IO.print("missing: " ++ show_reply(missing) ++ "\n")
    echo : Maybe<&2, List<&2, U32>> <- H.http.post_url("http://127.0.0.1:4480/echo", "application/ocsp-request", H.http.b("ping-body"))
    IO.print("echo: " ++ show_reply(echo) ++ "\n")
