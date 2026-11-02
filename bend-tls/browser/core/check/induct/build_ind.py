# Builds Ind.lean: the repo's Relay.lean (up to its main), the timed model, and the induction files named on the
# command line, in order. Then: lean Ind.lean (no sorry in the induction files; the build checks them).
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(HERE, '..', 'Relay.lean')).read()
cut = src.index("def main (args : List String) : IO UInt32 := do")
timed = open(os.path.join(HERE, 'timed_section.lean')).read()
tcut = timed.index("def main (args : List String) : IO UInt32 := do")
parts = [src[:cut], timed[:tcut]] + [open(os.path.join(HERE, p)).read() for p in sys.argv[1:]]
parts.append("\ndef main (args : List String) : IO UInt32 := do\n  IO.println \"ind\"\n  return 0\n")
open(os.path.join(HERE, 'Ind.lean'), 'w').write("".join(parts))
print("built Ind.lean")
