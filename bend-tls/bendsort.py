# Reorders the top-level definitions of a Bend file so that every definition
# comes after the definitions it refers to (Bend needs definitions before use).
# Text before the first "def" or "type" (imports, comments) and the type
# declarations stay in place; defs are emitted in dependency order.
import re

def split_blocks(src):
    head, blocks, cur = [], [], None
    for line in src.split("\n"):
        if re.match(r"^(def|type|law) ", line):
            if cur is not None:
                blocks.append(cur)
            cur = [line]
        elif cur is None:
            head.append(line)
        else:
            cur.append(line)
    if cur is not None:
        blocks.append(cur)
    return head, blocks

def name_of(block):
    m = re.match(r"^(?:def|type|law) ([^\s(:{]+)", block[0])
    return m.group(1) if m else None

def sort_defs(src):
    head, blocks = split_blocks(src)
    names = {name_of(b): i for i, b in enumerate(blocks)}
    deps = []
    for b in blocks:
        body = "\n".join(b[1:])
        text = "\n".join(ln for ln in b if not ln.lstrip().startswith("#"))
        refs = set()
        for n in names:
            if n and n != name_of(b) and re.search(r"(?<![\w.])" + re.escape(n) + r"(?![\w.])", text):
                refs.add(n)
        deps.append(refs)
    order, done, visiting = [], set(), set()
    def visit(n):
        if n in done:
            return
        if n in visiting:
            raise SystemExit(f"cycle through {n}")
        visiting.add(n)
        for d in sorted(deps[names[n]]):
            visit(d)
        visiting.discard(n)
        done.add(n)
        order.append(names[n])
    for n in names:
        if n:
            visit(n)
    seen = set(order)
    rest = [i for i in range(len(blocks)) if i not in seen]
    out = head[:]
    for i in order + rest:
        out.append("\n".join(blocks[i]))
    return "\n".join(out)
