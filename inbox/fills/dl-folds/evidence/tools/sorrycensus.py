#!/usr/bin/env python3
"""Sorry census of a sweep: per module, the declarations whose check reported
`declaration uses 'sorry'`, read from the newest log of each module.

usage: sorrycensus.py ORDER LOGDIR [LOGDIR ...]   (earlier LOGDIRs take precedence)

Each warning `F.lean:L:C: warning: declaration uses 'sorry'` is mapped to the declaration that
starts at line L of the working-tree source F (the name after the declaration keyword).
Output: one line `module: count: name, name` per module with sorries, then `TOTAL n in m modules`.
"""
import os, re, sys

ROOT = "/workspace/folds"
order = [l.strip() for l in open(sys.argv[1]) if l.strip()]
dirs = sys.argv[2:]
KW = re.compile(r"(?:theorem|lemma|def|instance|abbrev|structure|noncomputable def)\s+([^\s(:{\[]+)")
total, mods = 0, 0
for m in order:
    lg = None
    for d in dirs:
        p = f"{d}/{m.replace('/', '.')}.log"
        if os.path.exists(p):
            lg = p
            break
    if lg is None:
        print(f"MISSING LOG {m}")
        continue
    lines = open(f"{ROOT}/{m}.lean").read().splitlines()
    names = []
    for w in re.finditer(r"\.lean:(\d+):\d+: warning: declaration uses 'sorry'", open(lg).read()):
        ln = int(w.group(1))
        mm = KW.search(lines[ln - 1])
        names.append(mm.group(1) if mm else f"?line{ln}")
    if names:
        total += len(names)
        mods += 1
        print(f"{m}: {len(names)}: {', '.join(names)}")
print(f"TOTAL {total} in {mods} modules")
