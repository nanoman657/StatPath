// WebTCP.accept and try_accept: not supported in a page (95), since there is no listener to accept on.
function web_tcp_accept(listener, k) {
  return io_tup(listener, io_fail(95));
}

function web_tcp_try_accept(listener, ms, k) {
  return io_tup(listener, io_ready(performance.now() + Number(ms), io_fail(95)));
}

io_eff(CID(WebTCP.accept), web_tcp_accept);
io_eff(CID(WebTCP.try_accept), web_tcp_try_accept);
