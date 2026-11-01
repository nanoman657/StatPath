# Repeatedly runs bend --check-only on FILE and, when a parameter is reported as
# used more than once, adds "+" to that parameter in its definition's header.
import re, subprocess, sys
path = sys.argv[1]
for _ in range(60):
    out = subprocess.run(["bend", path, "--check-only"], capture_output=True, text=True).stdout + \
          subprocess.run(["bend", path, "--check-only"], capture_output=True, text=True).stderr
    m = re.search(r"expected : (\S+)\n- observed : \S+ \(consumed more than once\)", out)
    loc = re.search(r"Location: ?(\S+)?", out)
    if not m:
        print(out.strip().split("\n")[0:6])
        break
    name = m.group(1)
    d = re.search(r"Location:\s*\n?\s*\d+\s*\|?.*?\n(?:.*\n)*?", out)
    # find the defining header line: the nearest "def" line above the caret report
    lines = open(path).read().split("\n")
    # locate the line number shown in the report (line with the caret)
    ln = re.search(r"\n(\d+)>\|", out)
    if not ln:
        print("no location"); break
    idx = int(ln.group(1)) - 1
    while idx >= 0 and not lines[idx].startswith("def "):
        idx -= 1
    header = lines[idx]
    new = re.sub(r"(?<=[(,\s])(%s): " % re.escape(name), r"+\1: ", header, count=1)
    if new == header:
        print("could not patch", name, "in", header[:80]); break
    lines[idx] = new
    open(path, "w").write("\n".join(lines))
    print("patched", name, "in", new.split("(")[0])
