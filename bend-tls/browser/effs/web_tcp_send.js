// WebTCP.send and its forms: placeholders (ENOSYS, 38); the data comes back as the unsent bytes.
function web_tcp_send(socket, data, k) {
  return io_tup(socket, io_fail(38, data));
}

function web_tcp_try_send(socket, data, ms, k) {
  return io_tup(socket, io_ready(performance.now() + Number(ms), io_fail(38, data)));
}

io_eff(CID(WebTCP.send), web_tcp_send);
io_eff(CID(WebTCP.send_bytes), web_tcp_send);
io_eff(CID(WebTCP.try_send), web_tcp_try_send);
io_eff(CID(WebTCP.try_send_bytes), web_tcp_try_send);
