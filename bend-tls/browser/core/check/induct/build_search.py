# Builds Search.lean: the same model, the bounded-search checks (inv_checks.lean) and the search driver
# (search_main.lean). Run: lean --run Search.lean <depth>
import os
HERE = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(HERE, '..', 'Relay.lean')).read()
cut = src.index("def main (args : List String) : IO UInt32 := do")
timed = open(os.path.join(HERE, 'timed_section.lean')).read()
tcut = timed.index("def main (args : List String) : IO UInt32 := do")
checks = open(os.path.join(HERE, 'inv_checks.lean')).read()
main = open(os.path.join(HERE, 'search_main.lean')).read()
open(os.path.join(HERE, 'Search.lean'), 'w').write(src[:cut] + timed[:tcut] + checks + "\n" + main)
print("built Search.lean")
