"""Cut check for a landing unit with appended, whole-file and moved parts (standard library only).

Usage: python3 -I cutcheck2.py <unit.lean> <worktree> <outdir> [<extras.lean>]

This extends `audits/evidence/stage2-gate/scripts/cutcheck.py`. The unit is split into parts at
lines starting with HEADER. Each part names its landing module (`-- @landing M`), its imports
(`-- @imports a b ...`, possibly several lines) and optionally the module it moves declarations
from (`-- @moved-from M0`). The part's body is everything after its last `-- @` line.

A part is **new** when its landing module does not exist in the worktree, **appended** when it
exists and the part lists it among its imports, and a **whole-file replacement** when it exists
and the part does not list it.

For every part P this writes <outdir>/<M>[.partN].check.lean: the copyright block, the imports,
the standard options, and the bodies of the parts in P's import closure, in unit order. The
closure is computed over the real import graph: from P's imports, a module that is the landing
module of an earlier part pulls in that part (and the part's imports); a module that exists and is
not replaced by an included part is an existing module, and its own imports (read from the
worktree) are followed too. So an appended part reaches every check whose closure contains its
module, through existing modules as well as through parts. Two rules keep the check sound:

* a `-- @moved-from M0` part is omitted from a check whose existing modules include M0, since the
  old copy is then already imported (its body is identical; `identity.py` checks that);
* no existing module of a check may import a module that an included part replaces (the old file
  would then be imported beside its replacement): the script stops if one does.

An extras file has the same format. Its parts are checked after the unit's, with the unit's parts
available to their closures; an extras part may also say `-- @exclude-parts 4 5` to drop unit
parts (a whole-file check that already contains an appended part, or a probe that keeps an old
module), and `-- @with 106` to make an earlier extras part available.
"""
import os
import re
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


def mod_path(wt, mod):
    rel = os.path.join(*mod.split(".")) + ".lean"
    if os.path.isfile(os.path.join(wt, rel)):
        return os.path.join(wt, rel)
    pk = os.path.join(wt, ".lake", "packages")
    for d in os.listdir(pk):
        if os.path.isfile(os.path.join(pk, d, rel)):
            return os.path.join(pk, d, rel)
    return None


GRAPH = {}


def graph_imports(wt, mod):
    """Imports of an existing module, for TCSlib modules (other packages cannot import TCSlib)."""
    if not mod.startswith("TCSlib"):
        return []
    if mod not in GRAPH:
        p = mod_path(wt, mod)
        GRAPH[mod] = [m.group(1) for m in
                      (re.match(r"^import\s+(\S+)", l) for l in open(p, encoding="utf-8"))
                      if m] if p else []
    return GRAPH[mod]


def parse(path, base_index=0):
    lines = open(path, encoding="utf-8").read().split("\n")
    starts = [i for i, l in enumerate(lines) if l.startswith(HEADER)]
    parts = []
    for n, s in enumerate(starts):
        e = starts[n + 1] if n + 1 < len(starts) else len(lines)
        block = lines[s:e]
        land = [l.split()[2] for l in block if l.startswith("-- @landing ")]
        assert len(land) == 1, f"{path}: part at line {s + 1}: one @landing line expected"
        imps = [w for l in block if l.startswith("-- @imports ") for w in l.split()[2:]]
        moved = [l.split()[2] for l in block if l.startswith("-- @moved-from ")]
        excl = [int(w) for l in block if l.startswith("-- @exclude-parts ") for w in l.split()[2:]]
        with_ = [int(w) for l in block if l.startswith("-- @with ") for w in l.split()[2:]]
        last = max(i for i, l in enumerate(block) if l.startswith("-- @"))
        parts.append({"land": land[0], "imports": imps, "moved": moved[0] if moved else None,
                      "exclude": excl, "with": with_, "body": block[last + 1:], "line": s + 1,
                      "index": base_index + n + 1, "file": os.path.basename(path)})
    return parts


def kind(wt, p):
    if mod_path(wt, p["land"]) is None:
        return "new"
    return "append" if p["land"] in p["imports"] else "replace"


def check(wt, parts, k):
    """Closure, existing modules, imports and omitted parts for the check of parts[k]."""
    P = parts[k]
    included, E, seen = {k}, set(), set()
    queue = list(P["imports"])
    replaced = {P["land"]} if kind(wt, P) == "replace" else set()
    while queue:
        m = queue.pop()
        if m in seen:
            continue
        seen.add(m)
        here = [q for q in range(k) if parts[q]["land"] == m]
        for q in here:
            included.add(q)
            queue.extend(parts[q]["imports"])
            if kind(wt, parts[q]) == "replace":
                replaced.add(m)
        if m in replaced or mod_path(wt, m) is None:
            continue
        E.add(m)
        queue.extend(graph_imports(wt, m))
    # Ordering: a part landing in a module of the closure must precede the checked part.
    for q in range(k + 1, len(parts)):
        assert parts[q]["land"] not in seen or parts[q]["land"] == P["land"], (
            f"part {parts[q]['index']} ({parts[q]['land']}) is in the closure of part "
            f"{P['index']} but comes after it")
    for e in E:
        bad = set(graph_imports(wt, e)) & replaced
        assert not bad, f"check of part {P['index']}: existing {e} imports replaced {bad}"
    order = sorted(included)
    imps = []
    for q in order:
        for m in parts[q]["imports"]:
            if m not in replaced and mod_path(wt, m) is not None and m not in imps:
                imps.append(m)
            elif mod_path(wt, m) is None and not any(r["land"] == m for r in parts):
                raise SystemExit(f"part {parts[q]['index']}: import {m} is neither existing "
                                 f"nor a part")
    omitted = [q for q in order if parts[q]["moved"] and parts[q]["moved"] in E]
    return order, E, imps, omitted


def write(wt, parts, k, out, name):
    order, E, imps, omitted = check(wt, parts, k)
    path = os.path.join(out, name + ".check.lean")
    with open(path, "w", encoding="utf-8") as f:
        f.write(COPYRIGHT)
        f.write("".join(f"import {m}\n" for m in imps))
        f.write("\n" + OPTIONS + "\n")
        for q in order:
            if q in omitted:
                f.write(f"-- (part {parts[q]['index']} omitted: its old copy is imported from "
                        f"{parts[q]['moved']})\n\n")
                continue
            f.write("\n".join(parts[q]["body"]).rstrip("\n") + "\n\n")
    labels = ", ".join(f"{parts[q]['index']}" + ("(omitted)" if q in omitted else "")
                       for q in order)
    print(f"{name}: {kind(wt, parts[k])}; parts [{labels}]; {len(E)} existing modules in the "
          f"closure; imports {imps}")
    return path


def main():
    unit, wt, out = sys.argv[1], sys.argv[2], sys.argv[3]
    extras = sys.argv[4] if len(sys.argv) > 4 else None
    os.makedirs(out, exist_ok=True)
    parts = parse(unit)
    by_land = {}
    for p in parts:
        by_land.setdefault(p["land"], []).append(p)
    for k, p in enumerate(parts):
        name = p["land"] + (f".part{p['index']}" if len(by_land[p["land"]]) > 1 else "")
        write(wt, parts, k, out, name)
    if extras:
        xs = parse(extras, base_index=100)
        for x in xs:
            ps = ([p for p in parts if p["index"] not in x["exclude"]]
                  + [y for y in xs if y["index"] in x["with"]] + [x])
            write(wt, ps, len(ps) - 1, out, x["land"] + ".x" + str(x["index"]))


if __name__ == "__main__":
    main()
