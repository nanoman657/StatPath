# In-place dependency sort of a Bend file. The output is computed before the
# file is written, so a failure leaves the file as it was.
#   python3 -I sortfile.py FILE.bend
import sys
sys.path.insert(0, __file__.rsplit("/", 1)[0] if "/" in __file__ else ".")
from bendsort import sort_defs
path = sys.argv[1]
src = open(path).read()
out = sort_defs(src)
open(path, "w").write(out)
print("sorted", path)
