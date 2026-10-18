"""B6 hosts statement gate: landing and cut checks (read-only on the worktree; standard library).

Usage:
  python3 -I gate.py land <unit.lean> <worktree> <edits.py> <outdir>
  python3 -I gate.py cut  <unit.lean> <worktree> <edits.py> <outdir>

The unit is split into parts at header lines starting with HEADER. Each part names its landing
module (`-- @landing M`), its placement for an existing module (`-- @place append`,
`-- @place insert-before <line prefix>`, `-- @place insert-after <line>`,
`-- @place replace <declaration line>`) and its imports (`-- @imports a b ...`, possibly several
lines). The part's body is everything after its last marker line up to the next header.

`land` writes <outdir>/landing/<path> for every new module (copyright block, the part's imports,
the standard options, the part verbatim) and <outdir>/patched/<path> for every existing module
touched (the part placed as its header says, then the asserted edits of <edits.py>, each of
which must match exactly once), and <outdir>/patches/<File>.patch is left to `diff -u`.

`cut` writes <outdir>/cut/<Module>.check.lean for every part and <outdir>/cut/<File>.patched.
check.lean for every patched existing module: the imports of the target and of the parts in
its import closure, the standard options, the bodies of those parts in file order, then the
target's own body. The import closure is computed over the worktree's import graph, so a part
appended to an existing module is included wherever that module is (transitively) imported. A
`replace` part is never included in another target (it would clash with the snapshot's own
declaration); no Lean declaration consumes the replaced theorem.
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


def rd(p):
    return open(p, encoding="utf-8").read()


def wr(p, s):
    os.makedirs(os.path.dirname(p), exist_ok=True)
    open(p, "w", encoding="utf-8").write(s)


def mod_path(m):
    return os.path.join(*m.split(".")) + ".lean"


def exists(wt, m):
    if os.path.isfile(os.path.join(wt, mod_path(m))):
        return True
    pk = os.path.join(wt, ".lake", "packages")
    return any(os.path.isfile(os.path.join(pk, d, mod_path(m))) for d in os.listdir(pk))


def graph(wt):
    g = {}
    for dp, _, fs in os.walk(os.path.join(wt, "TCSlib")):
        for f in fs:
            if f.endswith(".lean"):
                p = os.path.join(dp, f)
                m = os.path.relpath(p, wt)[:-5].replace(os.sep, ".")
                g[m] = [l.split()[1] for l in rd(p).split("\n") if l.startswith("import TCSlib")]
    g["TCSlib"] = [l.split()[1] for l in rd(os.path.join(wt, "TCSlib.lean")).split("\n")
                   if l.startswith("import TCSlib")]
    return g


def parse(unit):
    lines = rd(unit).split("\n")
    first_doc = next(i for i, l in enumerate(lines) if l.startswith("/-!"))
    head = [l.split()[1] for l in lines[:first_doc] if l.startswith("import ")]
    starts = [i for i, l in enumerate(lines) if l.startswith(HEADER)]
    parts = []
    for n, s in enumerate(starts):
        e = starts[n + 1] if n + 1 < len(starts) else len(lines)
        block = lines[s:e]
        land = [l.split()[2] for l in block if l.startswith("-- @landing ")]
        place = [l[len("-- @place "):] for l in block if l.startswith("-- @place ")]
        imps = [w for l in block if l.startswith("-- @imports ") for w in l.split()[2:]]
        last = max(i for i, l in enumerate(block) if l.startswith("-- @"))
        assert len(land) == 1 and len(place) <= 1, f"part at line {s + 1}"
        body = "\n".join(block[last + 1:]).strip("\n") + "\n"
        parts.append({"land": land[0], "place": place[0] if place else None, "imports": imps,
                      "body": body, "line": s + 1, "label": chr(ord("A") + n)})
    return head, parts


def inner(body):
    ls = body.strip("\n").split("\n")
    while ls and (re.match(r"^(namespace \S+|open .*)$", ls[0]) or not ls[0].strip()):
        ls.pop(0)
    while ls and (re.match(r"^end \S+$", ls[-1]) or not ls[-1].strip()):
        ls.pop()
    return "\n".join(ls) + "\n"


def place(orig, p):
    kind, _, arg = p["place"].partition(" ")
    ls = orig.split("\n")
    if kind == "append":
        return orig.rstrip("\n") + "\n\n" + p["body"]
    if kind == "insert-before":
        idx = [i for i, l in enumerate(ls) if l.startswith(arg)]
        assert len(idx) == 1, (p["land"], kind, idx)
        i = idx[0]
        return "\n".join(ls[:i]) + "\n" + inner(p["body"]) + "\n" + "\n".join(ls[i:])
    if kind == "insert-after":
        idx = [i for i, l in enumerate(ls) if l == arg]
        assert len(idx) == 1, (p["land"], kind, idx)
        i = idx[0] + 1
        return "\n".join(ls[:i]) + "\n\n" + inner(p["body"]).rstrip("\n") + "\n" + \
            "\n".join(ls[i:])
    if kind == "replace":
        idx = [i for i, l in enumerate(ls) if l == arg]
        assert len(idx) == 1, (p["land"], kind, idx)
        a = idx[0]
        d0 = max(i for i in range(a) if ls[i].startswith("/--"))
        assert not any(re.match(r"^(theorem|lemma|def) ", ls[i]) for i in range(d0, a))
        e = next(i for i in range(a, len(ls)) if ls[i] == "  sorry")
        return "\n".join(ls[:d0]) + "\n" + inner(p["body"]).rstrip("\n") + "\n" + \
            "\n".join(ls[e + 1:])
    raise SystemExit(f"unknown placement {kind}")


def load_edits(path):
    ns = {}
    exec(compile(rd(path), path, "exec"), ns)
    return ns["EDITS"]


def apply_edits(text, edits, name):
    for k, (old, new) in enumerate(edits):
        n = text.count(old)
        assert n == 1, f"{name}: edit {k} matches {n} times: {old[:60]!r}"
        text = text.replace(old, new)
    return text


def land(unit, wt, edits_path, out):
    head, parts = parse(unit)
    edits = load_edits(edits_path)
    news = {p["land"] for p in parts if not exists(wt, p["land"])}
    touched = {}
    for p in parts:
        path = mod_path(p["land"])
        if p["land"] in news:
            assert p["place"] is None, p["land"]
            imps = "".join(f"import {m}\n" for m in p["imports"])
            wr(os.path.join(out, "landing", path), COPYRIGHT + imps + "\n" + OPTIONS + "\n" + p["body"])
            print(f"new      {path}: part {p['label']}")
        else:
            assert p["place"], p["land"]
            src = touched.get(path, rd(os.path.join(wt, path)))
            touched[path] = place(src, p)
            print(f"placed   {path}: part {p['label']} ({p['place'].split()[0]})")
    for path, es in edits.items():
        src = touched.get(path, rd(os.path.join(wt, path)))
        touched[path] = apply_edits(src, es, path)
        print(f"edited   {path}: {len(es)} asserted edits")
    for path, text in touched.items():
        wr(os.path.join(out, "patched", path), text)
    return parts


def closure(g, mods, part_by_land, news):
    seen, todo = set(), list(mods)
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        if m in news:
            todo += part_by_land[m]["imports"]
        else:
            todo += g.get(m, [])
    return seen


def check_file(imps, bodies):
    return COPYRIGHT + "".join(f"import {m}\n" for m in imps) + "\n" + OPTIONS + "\n" + \
        "\n".join(b.rstrip("\n") + "\n" for b in bodies)


def cut(unit, wt, edits_path, out):
    head, parts = parse(unit)
    g = graph(wt)
    news = {p["land"] for p in parts if not exists(wt, p["land"])}
    by_land = {p["land"]: p for p in parts}
    assert len(by_land) == len(parts), "one part per landing module"
    union = []
    for p in parts:
        for m in p["imports"]:
            if m not in news and m not in union:
                union.append(m)
    print(f"unit imports: {len(head)}; union of the parts' existing imports: {len(union)}; "
          f"missing from unit: {[m for m in union if m not in head]}; "
          f"extra in unit: {[m for m in head if m not in union]}")
    os.makedirs(os.path.join(out, "cut"), exist_ok=True)

    def target(name, imps, own, body):
        clo = closure(g, imps, by_land, news)
        inc = [q for q in parts if q is not own and q["land"] in clo
               and (q["place"] is None or not q["place"].startswith("replace"))
               and not (own is not None and own["place"] is None and q["land"] == own["land"])]
        allimps = []
        for m in imps + [m for q in inc for m in q["imports"]]:
            if m not in news and m not in allimps:
                allimps.append(m)
        wr(os.path.join(out, "cut", name), check_file(allimps, [q["body"] for q in inc] + [body]))
        labels = ",".join(q["label"] for q in inc)
        print(f"{name}: parts [{labels}] + own; imports {len(allimps)}")

    for p in parts:
        target(p["land"] + ".check.lean", p["imports"], p, p["body"])
    edits = load_edits(edits_path)
    patched_paths = sorted({mod_path(p["land"]) for p in parts if p["land"] not in news} |
                           set(edits))
    for path in patched_paths:
        text = rd(os.path.join(out, "patched", path))
        ls = text.split("\n")
        imps = [l.split()[1] for l in ls if l.startswith("import ")]
        doc = next(i for i, l in enumerate(ls) if l.startswith("/-!"))
        k = max([i for i in range(doc) if ls[i].startswith("set_option ")] or
                [i for i in range(doc) if ls[i].startswith("import ")])
        body = "\n".join(ls[k + 1:]).strip("\n") + "\n"
        m = path[:-5].replace(os.sep, ".")
        own = by_land.get(m)
        target(os.path.basename(path)[:-5] + ".patched.check.lean", imps,
               own if own is not None else {"place": "self", "land": m}, body)


if __name__ == "__main__":
    cmd, unit, wt, edits_path, out = sys.argv[1:6]
    if cmd == "land":
        land(unit, wt, edits_path, out)
    elif cmd == "cut":
        cut(unit, wt, edits_path, out)
    else:
        raise SystemExit("usage: land|cut")
