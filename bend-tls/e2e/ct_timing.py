#!/usr/bin/env python3
# Timing experiment for the X25519 ladder of the native build (ct_timing_x25519.bend).
# Three classes of scalar: all bits set, only the top bit set, and random. A constant-time
# ladder takes the same time for each class. Each run is one process; its CPU time (user plus
# system, from wait4) is recorded. The runs alternate between classes so drift affects them
# equally. The result is a Welch t-statistic per pair of classes: |t| above about 4.5 is the
# usual sign of a dependence (the dudect convention). This is an indicative measurement on a
# shared machine, not a proof.
#   bend ct_timing_x25519.bend -o ct_timing_x25519
#   python3 -I e2e/ct_timing.py ./ct_timing_x25519 [runs-per-class]
#   bend ct_timing_p256.bend -o ct_timing_p256
#   python3 -I e2e/ct_timing.py ./ct_timing_p256 [runs-per-class] p256
# The scalars are passed as 64 hex digits: X25519 reads them least significant byte first, P-256
# big-endian with the top bit clear (below n).
import math
import os
import random
import statistics
import subprocess
import sys


def run_once(binary, scalar):
    p = subprocess.Popen([binary, str(scalar)], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    _, status, usage = os.wait4(p.pid, 0)
    out = p.stdout.read().decode().strip()
    err = p.stderr.read().decode().strip()
    p.stdout.close()
    p.stderr.close()
    if status != 0:
        raise SystemExit(f"the program failed (wait status {status}) for scalar {scalar!r}: {out!r} {err[-300:]!r}")
    return usage.ru_utime + usage.ru_stime, out


def welch(a, b):
    ma, mb = statistics.fmean(a), statistics.fmean(b)
    va, vb = statistics.variance(a), statistics.variance(b)
    se = math.sqrt(va / len(a) + vb / len(b))
    return (ma - mb) / se if se > 0 else float("inf")


def main():
    binary = sys.argv[1]
    runs = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    curve = sys.argv[3] if len(sys.argv) > 3 else "x25519"
    rng = random.Random(1)
    if curve == "p256":
        # big-endian: the top byte is the most significant, and its top bit is clear
        classes = {
            "all-ones": "7f" + "ff" * 31,
            "top-bit": "40" + "00" * 31,
            "random": "%02x" % (rng.getrandbits(8) & 0x7F) + rng.getrandbits(248).to_bytes(31, "big").hex(),
        }
    else:
        classes = {
            "all-ones": "ff" * 31 + "7f",
            "top-bit": "00" * 31 + "40",
            "random": rng.getrandbits(256).to_bytes(32, "little").hex(),
        }
    print(f"curve: {curve}")
    times = {name: [] for name in classes}
    outs = {}
    for _ in range(runs):
        for name, scalar in classes.items():
            t, out = run_once(binary, scalar)
            times[name].append(t)
            outs.setdefault(name, out)
    print(f"runs per class: {runs}")
    for name in classes:
        xs = times[name]
        print(f"{name:9s} mean {statistics.fmean(xs) * 1000:8.2f} ms  "
              f"sd {statistics.stdev(xs) * 1000:7.2f} ms  (first output byte {outs[name]})")
    pairs = [("all-ones", "top-bit"), ("all-ones", "random"), ("top-bit", "random")]
    for a, b in pairs:
        t = welch(times[a], times[b])
        print(f"Welch t, {a} vs {b}: {t:+.2f}")
    worst = max(abs(welch(times[a], times[b])) for a, b in pairs)
    print(f"largest |t|: {worst:.2f} (about 4.5 or more suggests a dependence on the scalar)")


if __name__ == "__main__":
    main()
