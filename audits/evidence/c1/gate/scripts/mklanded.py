"""Write each landing module as it would land (read-only on the unit and the worktree):
a new module is the copyright block, the imports its part lists, the standard options and the
part verbatim; an addition to an existing module is that module with the part's extra imports
added after its own and the part appended. Output tree: <out>/TCSlib/... ."""
import os
import sys

unit, wt, out = sys.argv[1], sys.argv[2], sys.argv[3]
HEADER = "/-! ════"
COPYRIGHT = ("/-\nCopyright (c) 2026 Seyoon Ragavan. All rights reserved.\n"
             "Released under Apache 2.0 license as described in the file LICENSE.\n"
             "Authors: Seyoon Ragavan\n-/\n")
OPTIONS = ("set_option maxHeartbeats 0\nset_option relaxedAutoImplicit false\n"
           "set_option autoImplicit false\n")
lines = open(unit, encoding="utf-8").read().split("\n")
starts = [i for i, l in enumerate(lines) if l.startswith(HEADER)]
for n, s in enumerate(starts):
    e = starts[n + 1] if n + 1 < len(starts) else len(lines)
    block = lines[s:e]
    land = [l.split()[2] for l in block if l.startswith("-- @landing ")][0]
    imps = [w for l in block if l.startswith("-- @imports ") for w in l.split()[2:]]
    last = max(i for i, l in enumerate(block) if l.startswith("-- @imports "))
    body = "\n".join(block[last + 1:]).strip("\n") + "\n"
    rel = os.path.join(*land.split(".")) + ".lean"
    dst = os.path.join(out, rel)
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    src_path = os.path.join(wt, rel)
    if os.path.isfile(src_path):
        orig = open(src_path, encoding="utf-8").read()
        olines = orig.split("\n")
        lastimp = max(i for i, l in enumerate(olines) if l.startswith("import "))
        have = {l.split()[1] for l in olines if l.startswith("import ")}
        extra = [m for m in imps if m != land and m not in have]
        olines[lastimp + 1:lastimp + 1] = [f"import {m}" for m in extra]
        text = "\n".join(olines).rstrip("\n") + "\n\n" + body
        kind = f"existing module + {len(extra)} import(s) + appended part"
    else:
        text = COPYRIGHT + "".join(f"import {m}\n" for m in imps) + "\n" + OPTIONS + "\n" + body
        kind = "new module"
    open(dst, "w", encoding="utf-8").write(text)
    print(f"{rel}: {kind}; {len(text.splitlines())} lines")
