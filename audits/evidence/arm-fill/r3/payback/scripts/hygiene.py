"""Widths, Lean hygiene and cut identity of the dedup payback landing (read-only; stdlib only).

Usage: python3 -I -B hygiene.py <base export> <L>

1. Widths: every added line of the patches has at most 100 columns (code points).
2. Hygiene: none of `#eval`, `run_cmd`, `IO`, `unsafe`, `implemented_by`, `extern`,
   `native_decide`, `syntax`, `macro` or `elab` (as commands) in the code of the patches' added
   lines (comments blanked, so prose such as "the syntax scan" is not a command).
3. Cut identity: each inlined region of a cut file is the landed (or base, for an unchanged
   module) text after its imports, byte for byte; each delta declaration is the landed
   declaration's text; each probe Ax<key>.lean begins with its cut, byte for byte.
Exit 1 on any failure.
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lib  # noqa: E402
import edits as E  # noqa: E402
import cuts  # noqa: E402

BAD = re.compile(r"#eval|run_cmd|\bIO\b|\bunsafe\b|implemented_by|\bextern\b|native_decide|"
                 r"^\s*(?:syntax|macro|macro_rules|elab|elab_rules)\b", re.M)


def main():
    base, L = sys.argv[1:3]
    tree = os.path.join(L, "tree")
    fails = []
    print("## 1. Widths of the added lines")
    tot = 0
    for k in E.FILES:
        p = lib.rd(os.path.join(L, "patches", k + ".patch")).split("\n")
        a = [l[1:] for l in p if l.startswith("+") and not l.startswith("+++")]
        tot += len(a)
        over = [l for l in a if len(l) > 100]
        print(f"{k}: {len(a)} added lines, widest {max((len(l) for l in a), default=0)}, "
              f"over 100: {len(over)}")
        for l in over:
            print(f"   {len(l)}: {l[:110]}")
        if over:
            fails.append(f"width {k}")
    print(f"added lines: {tot}")
    print("\n## 2. Lean hygiene of the added lines")
    hits = []
    for k, (rel, _, _) in E.FILES.items():
        t = lib.rd(os.path.join(tree, rel))
        bl = set(lib.rd(os.path.join(base, rel)).split("\n"))
        for cl, rl in zip(lib.blank_comments(t).split("\n"), t.split("\n")):
            if rl not in bl:
                hits += [(k, m.group(0)) for m in BAD.finditer(cl)]
    print(f"scanned every tree line not in its base file; hits: {hits}")
    if hits:
        fails.append("hygiene")
    print("\n## 3. Cut identity")
    meta = json.loads(lib.rd(os.path.join(L, "work", "cut", "cuts.json")))
    nreg = 0
    for key, m in meta.items():
        cut = lib.rd(os.path.join(L, "work", "cut", m["file"])).split("\n")
        for r in m["regions"]:
            seg = "\n".join(cut[r["start"] - 1:r["end"]])
            if r["kind"] == "inline":
                rel = lib.path_of_mod(r["module"])
                src = os.path.join(tree, rel) if os.path.isfile(os.path.join(tree, rel)) else \
                    os.path.join(base, rel)
                ok = seg.strip("\n") == cuts.body_after_imports(lib.rd(src)).strip("\n")
            else:
                k2 = next(k for k in E.FILES if cuts.mod(k) == r["module"])
                t2 = lib.rd(os.path.join(tree, E.FILES[k2][0]))
                names = [n for _, ns, _ in E.DELTAS[k2]["groups"] for n in ns]
                ok = all(lib.decl_text(t2, n, cuts.TMP) in seg for n in names)
            nreg += 1
            if not ok:
                fails.append(f"cut {key} region {r['module']}")
                print(f"FAIL {key}: region {r['module']} ({r['kind']})")
        ax = os.path.join(L, "work", "probes", f"Ax{key}.lean")
        if not lib.rd(ax).startswith("\n".join(cut)):
            fails.append(f"probe Ax{key}")
            print(f"FAIL Ax{key}.lean does not begin with its cut")
    print(f"cut files {len(meta)}, regions checked {nreg}; probes begin with their cuts")
    print("\nRESULT:", "PASS" if not fails else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
