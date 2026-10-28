"""Remove the simp arguments Lean reports unused. Usage: fix_unused_simp.py <lean-output> <file>
Each warning `<file>:<line>:<col>: warning: This simp argument is unused:` is followed by the
argument's text; it is removed at that position with its separating comma."""
import re
import sys
out, path = sys.argv[1:3]
lines = open(out).read().split("\n")
src = open(path).read().split("\n")
hits = []
for i, l in enumerate(lines):
    m = re.match(r"^(\S+?):(\d+):(\d+): warning: This simp argument is unused:", l)
    if m and m.group(1).endswith(path.split("/")[-1]):
        arg = lines[i + 1].strip()
        hits.append((int(m.group(2)), int(m.group(3)), arg))
# right to left within a line so columns stay valid
for ln, col, arg in sorted(hits, key=lambda h: (h[0], -h[1])):
    l = src[ln - 1]
    # Lean columns count codepoints
    assert l[col:col + len(arg)] == arg, (ln, col, arg, l)
    before, after = l[:col], l[col + len(arg):]
    if after.startswith(", "):
        after = after[2:]
    elif before.endswith(", "):
        before = before[:-2]
    src[ln - 1] = before + after
open(path, "w").write("\n".join(src))
print(f"removed {len(hits)} unused simp arguments")
