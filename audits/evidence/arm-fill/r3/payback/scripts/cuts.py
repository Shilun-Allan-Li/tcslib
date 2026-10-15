"""Cut files of the changed modules (read-only on the base; standard library only).

Usage: python3 -I cuts.py [<tree dir> <out dir>] [--only K1,K2]

The snapshot's oleans are the base's, so a changed module that imports another changed module
cannot be elaborated against the snapshot by itself. The cut method of the MIG-1 S landing is
extended to the two kinds of change in this landing:

* **Additive changes** (new or promoted public declarations, proof changes, private
  deletions, a new import): an upstream module A of this kind is loaded from the snapshot,
  and the cut adds A's **delta** after the imports: the landed text of A's new public
  declarations (copied from the landed file, asserted identical), in A's namespace context,
  and A's new imports. Every other use of A sees A's unchanged public statements.
* **Restatements** (D1: `InWin` -> `Turing.Cfg.InWindow` in the public statements of
  `Codec/{Word,Valid,Step,Langs,Checks,Bridge}` and `ExpBFS/Radius`): the snapshot's oleans of
  these modules and of every module downstream of them are stale, so the cut **inlines** the
  landed text of every module of X's import closure that is downstream of a restated module
  (changed or not), in topological order, and loads none of them.

The cut of a changed module X: the copyright block; the union of the inlined modules' imports
that are not inlined, with the deltas' new imports (each asserted not downstream of a restated
module, so that its snapshot olean is current up to additions); the standard options; the
deltas of every changed module upstream of X that is not inlined; the bodies (text after the
imports) of the inlined modules, X last. cuts.json records each cut's regions (line ranges),
which are compared with the base elaborations of the same modules (verify.py).
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lib  # noqa: E402
import edits as E  # noqa: E402

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
TMP = os.path.join(lib.L, "work", "tmp-scan")


def mod(key):
    return lib.mod_of_path(E.FILES[key][0])


def body_after_imports(text):
    ls = text.split("\n")
    last = max(i for i, l in enumerate(ls) if l.startswith("import "))
    return "\n".join(ls[last + 1:]).strip("\n") + "\n"


def delta_text(key, tree):
    d = E.DELTAS[key]
    t = lib.rd(os.path.join(tree, E.FILES[key][0]))
    parts = []
    for opn, names, cls in d["groups"]:
        decls = [lib.decl_text(t, n, TMP) for n in names]
        parts.append(opn + "\n\n".join(decls) + "\n\n" + cls)
    return "\n".join(parts)


def sorried(text):
    ds, ls = lib.scan_text(text, TMP)
    out = []
    for d in ds:
        if re.search(r"\bsorry\b", lib.strip_comments("\n".join(ls[d["line"] - 1:d["end"]]))):
            out.append(d["name"])
    return out


def build(key, tree, base, gl, keys_by_mod, X=None, own_only=False):
    X = X or mod(key)
    R = [mod(k) for k in E.RESTATED]
    DR = lib.down(gl, R)
    upX = lib.up(gl, [X])
    inl = [X] if own_only else lib.topo(gl, (upX & DR) | {X})
    assert inl[-1] == X
    changed_up = [m for m in lib.topo(gl, upX - set(inl)) if m in keys_by_mod]
    deltas = [keys_by_mod[m] for m in changed_up if keys_by_mod[m] in E.DELTAS]
    src = {}
    for m in inl:
        rel = lib.path_of_mod(m)
        p = os.path.join(tree, rel) if os.path.isfile(os.path.join(tree, rel)) else \
            os.path.join(base, rel)
        src[m] = lib.rd(p)
    imps = []
    for m in inl:
        for i in lib.header_imports(src[m]):
            if i not in inl and i not in imps:
                imps.append(i)
    for k in deltas:
        for i in E.DELTAS[k]["imports"]:
            if i not in imps:
                imps.append(i)
    bad = [i for i in imps if i in DR]
    assert own_only or not bad, f"{key}: imports downstream of a restated module: {bad}"
    head = COPYRIGHT + "".join(f"import {i}\n" for i in imps) + "\n" + OPTIONS + "\n"
    text = head
    regions = []
    for k in deltas:
        dt = "/-! Delta of `" + mod(k) + "` (landed declarations, copied). -/\n\n" + \
            delta_text(k, tree) + "\n"
        a = text.count("\n") + 1
        text += dt
        regions.append({"module": mod(k), "kind": "delta", "start": a, "end": text.count("\n"),
                        "sorried": sorried(dt)})
    for m in inl:
        b = body_after_imports(src[m])
        a = text.count("\n") + 1
        text += b + "\n"
        regions.append({"module": m, "kind": "inline", "changed": m in keys_by_mod,
                        "start": a, "end": text.count("\n"), "sorried": sorried(b)})
    return text, {"key": key, "module": X, "inlined": inl, "deltas": [mod(k) for k in deltas],
                  "imports": imps, "regions": regions, "lines": text.count("\n"),
                  "expected_sorry": sum(len(r["sorried"]) for r in regions)}


def main():
    args = sys.argv[1:]
    only = None
    if "--only" in args:
        k = args.index("--only"); only = args[k + 1].split(","); args = args[:k] + args[k + 2:]
    tree = args[0] if args else lib.TREE
    out = args[1] if len(args) > 1 else os.path.join(lib.L, "work", "cut")
    base = lib.BASE
    gl = lib.graph(base, overlay=tree)
    keys_by_mod = {mod(k): k for k in E.FILES}
    os.makedirs(out, exist_ok=True)
    metap = os.path.join(out, "cuts.json")
    meta = json.loads(lib.rd(metap)) if os.path.isfile(metap) else {}
    jobs = [(k, None, k in E.OWN_TEXT_ONLY) for k in E.FILES] + \
        [("consumer-" + c.split(".")[-1], c, False) for c in E.CONSUMERS]
    for key, X, own in jobs:
        if only and key not in only:
            continue
        text, m = build(key, tree, base, gl, keys_by_mod, X, own)
        m["own_text_only"] = own
        name = f"{key}.cut.lean"
        lib.wr(os.path.join(out, name), text)
        m["file"] = name
        meta[key] = m
        print(f"{name}: {m['lines']} lines; inlined {len(m['inlined'])} "
              f"({', '.join(x.split('.')[-1] for x in m['inlined'])}); deltas "
              f"{[x.split('.')[-1] for x in m['deltas']]}; expected sorry {m['expected_sorry']}")
    lib.wr(metap, json.dumps(meta, indent=1) + "\n")


if __name__ == "__main__":
    main()
