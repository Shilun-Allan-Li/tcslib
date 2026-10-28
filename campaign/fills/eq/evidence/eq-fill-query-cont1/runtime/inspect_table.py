"""Inspection table, step 2: join the extracted identifiers with their resolution and classify.
Usage: inspect_table.py <inspect-idents.tsv> <inspect.out> <table.md>"""
import sys
idents, out, table = sys.argv[1:4]
res = {}
for l in open(out):
    p = l.rstrip("\n").split("\t")
    if len(p) == 4:
        res[p[0]] = p[1:]
rows, counts = [], {}
# manual review of the extractor's over-captures (an identifier inside a nested term of a
# bracket list is not a rewrite rule)
REVIEWED = {
    "Cfg.ofWords": "other file: definition named in a `show` goal that unfolds only the file's"
                   " own `qyM₁` to its `tm`; itself not unfolded (sealed copy elaborates; reviewed)",
    "phaseHostTM": "other file: definition named in `show` goals that unfold only the file's"
                   " own `qyM₁` to its `tm`; itself not unfolded (sealed copy elaborates; reviewed)",
    "Function.update": "Core/Mathlib: definition named in `show` goals and in the type of a `have`"
                       " nested in a `rw` list; never a rewrite rule or unfolded (reviewed)",
}
for l in open(idents):
    n, kinds, c, ln = l.rstrip("\n").split("\t")
    full, kind, mod = res.get(n, ["?", "?", "?"])
    tactic_only_show = set(kinds.split(",")) <= {"show", "change"}
    if mod == "(this file)":
        cls = "own file"
    elif n in REVIEWED:
        cls = REVIEWED[n]
    elif n == "reduceCtorEq":
        cls = "Core: simproc (constructor disequality), run by simp, not a definition unfolded"
    elif full == "-":
        cls = "local (hypothesis, binder or field)"
    elif mod.startswith("TCSlib"):
        if kind.startswith("theorem"):
            cls = "other file: theorem"
        elif "projection" in kind or kind in ("ctor", "inductive"):
            cls = f"other file: {kind} (structure field/constructor/type; not unfolded)"
        elif tactic_only_show:
            cls = "other file: definition named in a show/change goal (FINDING unless not unfolded)"
        else:
            cls = "other file: definition (FINDING)"
    else:
        if kind.startswith("theorem"):
            cls = "Core/Mathlib: theorem"
        elif "projection" in kind or kind in ("ctor", "inductive"):
            cls = f"Core/Mathlib: {kind}"
        elif tactic_only_show:
            cls = "Core/Mathlib: definition in show/change (reduces in a show step: allowed)"
        else:
            cls = "Core/Mathlib: definition in simp/rw/unfold (FINDING)"
    counts[cls] = counts.get(cls, 0) + 1
    rows.append((cls, n, full, kind, mod, kinds, c, ln))
rows.sort()
with open(table, "w") as f:
    f.write("| identifier | resolves to | kind | module | tactics | uses | first line | class |\n")
    f.write("|---|---|---|---|---|---|---|---|\n")
    for cls, n, full, kind, mod, kinds, c, ln in rows:
        f.write(f"| `{n}` | `{full}` | {kind} | {mod} | {kinds} | {c} | {ln} | {cls} |\n")
for k in sorted(counts):
    print(f"{counts[k]:4d}  {k}")
