// WebTCP.recv and its forms: placeholders (ENOSYS, 38).
function web_tcp_recv(socket, max, k) {
  return io_tup(socket, io_fail(38));
}

function web_tcp_try_recv(socket, max, ms, k) {
  return io_tup(socket, io_ready(performance.now() + Number(ms), io_fail(38)));
}

io_eff(CID(WebTCP.recv), web_tcp_recv);
io_eff(CID(WebTCP.recv_bytes), web_tcp_recv);
io_eff(CID(WebTCP.try_recv), web_tcp_try_recv);
io_eff(CID(WebTCP.try_recv_bytes), web_tcp_try_recv);
