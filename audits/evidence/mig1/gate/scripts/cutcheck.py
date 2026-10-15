"""Cut check for a gate elaboration unit (read-only; standard library only).

Usage: python3 -I cutcheck.py <unit.lean> <worktree> <outdir>

The unit is split into parts at header lines starting with HEADER. Each part names its landing
module (`-- @landing M`) and its imports (`-- @imports a b ...`, possibly several lines). The
part's body is everything after its last `-- @imports` line up to the next header.

For every part P this writes <outdir>/<M>.check.lean: the copyright block, the imports of P's
import closure that exist in the worktree, the standard options, and the bodies of the parts in
P's closure (P and every part whose landing module P imports, transitively), in file order. An
import that names an existing module and also the landing module of a part (a local modification
of a vendored file) both imports the module and pulls in the part. It also reports whether the
unit's own imports are exactly the union of the existing imports that the parts list.
"""
import os
import sys

HEADER = "/-! ════"
COPYRIGHT = """/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
"""
OPTIONS = """set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
"""


def exists(wt, mod):
    rel = os.path.join(*mod.split(".")) + ".lean"
    if os.path.isfile(os.path.join(wt, rel)):
        return True
    pk = os.path.join(wt, ".lake", "packages")
    return any(os.path.isfile(os.path.join(pk, d, rel)) for d in os.listdir(pk))


def main():
    unit, wt, out = sys.argv[1], sys.argv[2], sys.argv[3]
    lines = open(unit, encoding="utf-8").read().split("\n")
    first_doc = next(i for i, l in enumerate(lines) if l.startswith("/-!"))
    head_imports = [l.split()[1] for l in lines[:first_doc] if l.startswith("import ")]
    starts = [i for i, l in enumerate(lines) if l.startswith(HEADER)]
    parts = []
    for n, s in enumerate(starts):
        e = starts[n + 1] if n + 1 < len(starts) else len(lines)
        block = lines[s:e]
        land = [l.split()[2] for l in block if l.startswith("-- @landing ")]
        imps = [w for l in block if l.startswith("-- @imports ") for w in l.split()[2:]]
        last = max(i for i, l in enumerate(block) if l.startswith("-- @imports "))
        assert len(land) == 1, f"part at line {s + 1}: one @landing line expected"
        parts.append({"land": land[0], "imports": imps, "body": block[last + 1:], "line": s + 1})
    by_land = {}
    for k, p in enumerate(parts):
        by_land.setdefault(p["land"], []).append(k)
    union = []
    for p in parts:
        for m in p["imports"]:
            if exists(wt, m) and m not in union:
                union.append(m)
    missing_head = [m for m in union if m not in head_imports]
    extra_head = [m for m in head_imports if m not in union]
    print(f"unit imports: {len(head_imports)}; union of part imports: {len(union)}; "
          f"missing from unit: {missing_head}; extra in unit: {extra_head}")
    os.makedirs(out, exist_ok=True)
    for k, p in enumerate(parts):
        closure, todo = set(), [k]
        while todo:
            j = todo.pop()
            if j in closure:
                continue
            closure.add(j)
            for m in parts[j]["imports"]:
                for i in by_land.get(m, []):
                    if i < j:
                        todo.append(i)
        order = sorted(closure)
        imps = []
        for j in order:
            for m in parts[j]["imports"]:
                if exists(wt, m) and m not in imps:
                    imps.append(m)
                elif not exists(wt, m) and m not in by_land:
                    raise SystemExit(f"part {p['land']}: import {m} is neither existing nor a part")
        name = p["land"] + (f".part{k}" if len(by_land[p["land"]]) > 1 else "")
        path = os.path.join(out, name + ".check.lean")
        with open(path, "w", encoding="utf-8") as f:
            f.write(COPYRIGHT)
            f.write("".join(f"import {m}\n" for m in imps))
            f.write("\n" + OPTIONS + "\n")
            for j in order:
                f.write("\n".join(parts[j]["body"]).rstrip("\n") + "\n\n")
        labels = ", ".join(parts[j]["land"].split(".")[-1] + f"@{parts[j]['line']}" for j in order)
        print(f"{name}: closure [{labels}]; imports {imps}")


if __name__ == "__main__":
    main()
