"""Extend the import probe by every other-file TCSlib constant the walk reports that the probe
does not `#check` yet. Usage: gen_probe.py <probe.lean.txt> <walk.out> <out.lean>"""
import re
import sys
probe, walk, out = sys.argv[1:4]
src = open(probe).read().rstrip("\n").split("\n")
have = {l.split("@", 1)[1].strip() for l in src if l.startswith("#check @")}
add = []
for line in open(walk):
    m = re.match(r"^(theorem|def|inductive|ctor|rec|axiom|opaque|quot)\b[^\[]* (\S+) \[TCSlib", line)
    if not m:
        continue
    n = m.group(2)
    if n in have or n in add or "_sizeOf_inst" in n or ".match_" in n or "._proof" in n:
        continue
    add.append(n)
body = src + ["", "/-! The fill's citations beyond the brief's list (from the elaborated-constant walk). -/", ""] + \
    [f"#check @{n}" for n in sorted(add)] + [""]
open(out, "w").write("\n".join(body))
print(f"probe: {len(have)} original names + {len(add)} added = {len(have) + len(add)} checks")
