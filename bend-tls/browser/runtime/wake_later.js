// test effect: completes with ms after a host timer fires, with no file descriptor. The timer
// calls io_notify; more() re-parks itself until the value is ready.
function wake_later(ms, k) {
  let ready;
  const more = () => {
    if (ready === undefined) {
      io_park_on(undefined, false, k, more, Infinity);
      return undefined;
    }
    return ready;
  };
  setTimeout(() => {
    ready = Number(ms);
    io_notify();
  }, Number(ms));
  io_park_on(undefined, false, k, more, Infinity);
}

io_eff(CID(Wake.later), wake_later);
