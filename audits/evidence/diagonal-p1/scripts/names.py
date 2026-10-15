"""Name screen for Diagonal Part 1 (read-only; standard library only).

Usage: python3 -I names.py <base root> <base Diagonal.lean> <landed Diagonal.lean>

Lists the new public names (declarations, plus the constructors and fields Lean generates for
the two structures), and screens every new name's distinctive component as a whole word over
every `.lean` file of the base tree (`<base root>/TCSlib`, `TCSlib.lean`): an occurrence would
be a collision or a downstream reference to a name that did not exist. Exit 1 on any hit.
"""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(__file__))
from decls import parse  # noqa: E402


def main():
    root, base_p, land_p = sys.argv[1:4]
    base = parse(open(base_p, encoding="utf-8").read())
    land = parse(open(land_p, encoding="utf-8").read())
    bn = {d["name"] for d in base}
    new = [d for d in land if d["name"] not in bn]
    names = [d["name"] for d in new]
    fields = {"Complexity.TimeHierarchy.DiagSimulator": ["mk", "W", "simulates"],
              "Complexity.TimeHierarchy.SelfSimulator": ["mk", "W", "decode", "simulates",
                                                         "normalForm"]}
    for s, fs in fields.items():
        assert s in names, f"structure {s} not found"
        names += [f"{s}.{f}" for f in fs]
    print(f"## New public names ({len(names)}: {len(new)} declarations, "
          f"{len(names) - len(new)} generated constructors and fields)")
    for n in names:
        print(f"- `{n}`")
    tokens = sorted({n.split(".")[2] for n in names})
    print()
    print(f"## Whole-word screen of the distinctive components over the base tree: {tokens}")
    files = [os.path.join(root, "TCSlib.lean")]
    for d, _, fs in os.walk(os.path.join(root, "TCSlib")):
        files += [os.path.join(d, f) for f in fs if f.endswith(".lean")]
    hits = []
    for f in sorted(files):
        src = open(f, encoding="utf-8").read()
        for t in tokens:
            for m in re.finditer(r"(?<![A-Za-z0-9_'.])" + re.escape(t) + r"(?![A-Za-z0-9_'])",
                                 src):
                line = src.count("\n", 0, m.start()) + 1
                hits.append(f"{os.path.relpath(f, root)}:{line}: {t}")
    print(f"files screened: {len(files)}; occurrences: {len(hits)}")
    for h in hits:
        print("  " + h)
    if hits:
        print("NAMES: FAIL")
        sys.exit(1)
    print("NAMES: PASS — no new name, constructor or field occurs anywhere in the base tree")


if __name__ == "__main__":
    main()
