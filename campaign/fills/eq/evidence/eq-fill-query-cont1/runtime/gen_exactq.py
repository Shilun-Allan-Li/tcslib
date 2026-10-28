"""Semantic duplication probe: a scratch copy of the owned module in which every new private
theorem's proof is replaced by `exact?`. Usage: gen_exactq.py <owned.lean> <out.lean> <map.tsv>
Writes the copy and a map `line<TAB>name` of each probe's `exact?` line."""
import re
import sys
owned, out, mp = sys.argv[1:4]
src = open(owned).read().split("\n")
i0 = next(i for i, l in enumerate(src) if l.startswith("private theorem qy_query_of_main"))
# region (b): from the first docstring after qy_query_of_main to the target's docstring
i1 = next(i for i in range(i0 + 1, len(src)) if src[i].startswith("/--"))
i2 = next(i for i, l in enumerate(src) if l.startswith("/-- **The stage query in linear time**"))
starts = [i for i in range(i1, i2) if src[i].startswith("/--")] + [i2]
res = src[:i1]
probes = []
for a, b in zip(starts, starts[1:]):
    chunk = src[a:b]
    k = next((j for j, l in enumerate(chunk) if l.startswith("private theorem ")), None)
    if k is None:
        res += chunk
        continue
    name = chunk[k].split()[2]
    text = "\n".join(chunk[k:])
    # the first `:=` at bracket depth 0 ends the statement
    depth, pos = 0, None
    for j, ch in enumerate(text):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif depth == 0 and text.startswith(":=", j):
            pos = j
            break
    assert pos is not None, name
    stmt = text[:pos].rstrip()
    decl_line = len(res) + k + 1  # 1-based line of `private theorem`, before the shift below
    res += chunk[:k] + (stmt + " := by\n  first | exact? | sorry").split("\n") + [""]
    probes.append((decl_line, name))
res += src[i2:]
s = "\n".join(res)
s = s.replace("set_option maxHeartbeats 0\n",
              "set_option maxHeartbeats 400000\nset_option maxErrors 100000\n", 1)
open(out, "w").write(s)
open(mp, "w").write("".join(f"{ln + 1}\t{n}\n" for ln, n in probes))  # +1: the maxErrors line
print(f"{len(probes)} probes")
