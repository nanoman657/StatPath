// WebTCP.listen: a page cannot accept incoming connections, so listen is not supported (95).
function web_tcp_listen(host, port, k) {
  return io_fail(95);
}

io_eff(CID(WebTCP.listen), web_tcp_listen);
