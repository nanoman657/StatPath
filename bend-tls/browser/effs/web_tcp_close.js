// WebTCP.close and close_listener: closing a socket or a listener that the page has none of is a
// no-op, so they return Unit.
function web_tcp_close(socket, k) {
  return { $: CID(Unit) };
}

io_eff(CID(WebTCP.close), web_tcp_close);
io_eff(CID(WebTCP.close_listener), web_tcp_close);
