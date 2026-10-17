"""Import graph of the base tree overlaid with the landed files: the downstream closure of the
landed modules, in topological order (never the root `TCSlib`). Read-only; standard library only.

Usage: python3 -I graph2.py <base root> <landed root> <olean root> <package lib dirs> <out dir>

Writes <out dir>/replay-order.txt. Fails (exit 1) if a listed module imports a module that is
neither listed earlier nor present as an olean in the snapshot or the packages.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(__file__))
from graph import imports_of  # noqa: E402


def scan(root):
    mods = {}
    for d, _, fs in os.walk(os.path.join(root, "TCSlib")):
        for f in fs:
            if f.endswith(".lean"):
                p = os.path.join(d, f)
                mods[os.path.relpath(p, root)[:-5].replace(os.sep, ".")] = imports_of(p)
    top = os.path.join(root, "TCSlib.lean")
    if os.path.isfile(top):
        mods["TCSlib"] = imports_of(top)
    return mods


def main():
    base, landed, olean_root, pkgs, out = sys.argv[1:6]
    mods = scan(base)
    over = scan(landed)
    mods.update(over)
    targets = sorted(over)
    rev = {}
    for m, imps in mods.items():
        for i in imps:
            rev.setdefault(i, set()).add(m)
    closure, todo = set(), list(targets)
    while todo:
        m = todo.pop()
        if m in closure:
            continue
        closure.add(m)
        todo.extend(rev.get(m, ()))
    closure.discard("TCSlib")
    indeg = {m: sum(1 for i in mods[m] if i in closure) for m in closure}
    ready = sorted(m for m in closure if indeg[m] == 0)
    order = []
    while ready:
        m = ready.pop(0)
        order.append(m)
        for n in sorted(rev.get(m, ())):
            if n in indeg:
                indeg[n] -= 1
                if indeg[n] == 0:
                    ready.append(n)
                    ready.sort()
    assert len(order) == len(closure), "cycle"
    libs = [olean_root] + [p for p in pkgs.split(":") if p]

    def has_olean(m):
        rel = os.path.join(*m.split(".")) + ".olean"
        return any(os.path.isfile(os.path.join(l, rel)) for l in libs)

    pos = {m: k for k, m in enumerate(order)}
    bad = []
    for m in order:
        for i in mods[m]:
            if i in pos:
                if pos[i] >= pos[m]:
                    bad.append(f"{m} imports {i} listed later")
            elif not has_olean(i):
                bad.append(f"{m} imports {i}: not listed and no olean")
    os.makedirs(out, exist_ok=True)
    open(os.path.join(out, "replay-order.txt"), "w").write(
        "\n".join(m.replace(".", "/") for m in order) + "\n")
    print(f"landed modules ({len(targets)}): " + ", ".join(targets))
    print(f"downstream closure: {len(order)} modules (root TCSlib excluded: {'TCSlib' not in order})")
    if bad:
        print("FAIL: " + "; ".join(bad[:20]))
        sys.exit(1)
    print("every import of every listed module is listed earlier or present as an olean: PASS")


if __name__ == "__main__":
    main()
