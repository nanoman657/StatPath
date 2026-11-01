// WebTCP.connect: placeholder until the relay client is wired in (ENOSYS, 38).
function web_tcp_connect(host, port, k) {
  return io_fail(38);
}

io_eff(CID(WebTCP.connect), web_tcp_connect);
