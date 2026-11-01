# tcp.bend: the TCP declarations of a page build. They have the signatures of Base's TCP
# (bend2/base.bend), under the names WebTCP.*, so a page program imports this module and calls
# WebTCP.connect where a native program calls TCP.connect. Each one imports a browser effect
# (effs/web_tcp_*.js) instead of the native C and JS files. The JavaScript effects are placeholders
# until they are written: connect and the send and receive forms answer ENOSYS (38), and listen and
# accept answer EOPNOTSUPP (95), since a page cannot accept an incoming connection.
#
#   bend tcp.bend --check-only    (checks the declarations and their imports)

import Base

def WebTCP.listen(host: String, port: U32) -> IO(Result<&1, &1, U32 & String, Listener>):
  import "./effs/web_tcp.js"

def WebTCP.accept(listener: Listener) ->
  IO(Listener & Result<&1, &1, U32 & String, Socket>):
  import "./effs/web_tcp.js"

def WebTCP.try_accept(listener: Listener, ms: U32) ->
  IO(Listener & Poll<&1, &1, Result<&1, &1, U32 & String, Socket>, Unit>):
  import "./effs/web_tcp.js"

def WebTCP.connect(host: String, port: U32) ->
  IO(Result<&1, &1, U32 & String, Socket>):
  import "./effs/web_tcp.js"

def WebTCP.send(sock: Socket, data: String) ->
  IO(Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit>):
  import "./effs/web_tcp.js"

def WebTCP.try_send(sock: Socket, data: String, ms: U32) ->
  IO(Socket & Poll<&1, &1, Result<&1, &1, (U32 & String) & List<&2, U32>, Unit>,
    List<&2, U32>>):
  import "./effs/web_tcp.js"

def WebTCP.recv(sock: Socket, max: U32) ->
  IO(Socket & Result<&1, &1, U32 & String, Maybe<&1, String>>):
  import "./effs/web_tcp.js"

def WebTCP.try_recv(sock: Socket, max: U32, ms: U32) ->
  IO(Socket & Poll<&1, &1, Result<&1, &1, U32 & String, Maybe<&1, String>>, Unit>):
  import "./effs/web_tcp.js"

def WebTCP.send_bytes(sock: Socket, data: List<&2, U32>) ->
  IO(Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit>):
  import "./effs/web_tcp.js"

def WebTCP.try_send_bytes(sock: Socket, data: List<&2, U32>, ms: U32) ->
  IO(Socket & Poll<&1, &1, Result<&1, &1, (U32 & String) & List<&2, U32>, Unit>,
    List<&2, U32>>):
  import "./effs/web_tcp.js"

def WebTCP.recv_bytes(sock: Socket, max: U32) ->
  IO(Socket & Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>>):
  import "./effs/web_tcp.js"

def WebTCP.try_recv_bytes(sock: Socket, max: U32, ms: U32) ->
  IO(Socket & Poll<&1, &1, Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>>,
    Unit>):
  import "./effs/web_tcp.js"

def WebTCP.close(socket: Socket) -> IO(Unit):
  import "./effs/web_tcp.js"

def WebTCP.close_listener(listener: Listener) -> IO(Unit):
  import "./effs/web_tcp.js"
