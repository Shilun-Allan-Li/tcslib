"""Import graph of the base tree: Diagonal's downstream closure, its replay order, and the
cut-check chains of its direct importers. Read-only; standard library only.

Usage: python3 -I graph.py <base root> <olean root> <package lib dirs, ':'-separated> <out dir>

Writes <out dir>/replay-order.txt (the downstream closure of
`TCSlib.Complexity.TimeHierarchy.Diagonal`, Diagonal first, in topological order, never the
root `TCSlib`) and <out dir>/chains.txt (for each direct importer: the modules of the closure
that it imports transitively, in topological order). Fails (exit 1) if a module of the list
imports a module that is neither in the list nor present as an olean in the snapshot or the
packages.
"""
import os
import sys

TARGET = "TCSlib.Complexity.TimeHierarchy.Diagonal"


def imports_of(path):
    """The `import` lines of a Lean file's header (after leading comments, before any code)."""
    src = open(path, encoding="utf-8").read()
    k, n, out = 0, len(src), []
    while k < n:
        if src[k].isspace():
            k += 1
        elif src.startswith("/-", k):
            depth, k = 1, k + 2
            while k < n and depth:
                if src.startswith("/-", k):
                    depth, k = depth + 1, k + 2
                elif src.startswith("-/", k):
                    depth, k = depth - 1, k + 2
                else:
                    k += 1
        elif src.startswith("--", k):
            e = src.find("\n", k)
            k = n if e < 0 else e
        elif src.startswith("import ", k):
            e = src.find("\n", k)
            e = n if e < 0 else e
            out.extend(src[k + 7:e].split("--")[0].split())
            k = e
        else:
            break
    return out


def main():
    root, olean_root, pkgs, out = sys.argv[1:5]
    mods = {}
    for d, _, fs in os.walk(os.path.join(root, "TCSlib")):
        for f in fs:
            if f.endswith(".lean"):
                p = os.path.join(d, f)
                m = os.path.relpath(p, root)[:-5].replace(os.sep, ".")
                mods[m] = imports_of(p)
    mods["TCSlib"] = imports_of(os.path.join(root, "TCSlib.lean"))
    rev = {}
    for m, imps in mods.items():
        for i in imps:
            rev.setdefault(i, set()).add(m)
    closure, todo = set(), [TARGET]
    while todo:
        m = todo.pop()
        if m in closure:
            continue
        closure.add(m)
        todo.extend(rev.get(m, ()))
    closure.discard("TCSlib")
    # topological order (Kahn, ties by name)
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
    assert len(order) == len(closure), "cycle in the closure"
    assert order[0] == TARGET, f"first module is {order[0]}"
    # every import listed or available as an olean
    libs = [olean_root] + [p for p in pkgs.split(":") if p]

    def has_olean(m):
        rel = os.path.join(*m.split(".")) + ".olean"
        return any(os.path.isfile(os.path.join(l, rel)) for l in libs)

    bad = []
    pos = {m: k for k, m in enumerate(order)}
    for m in order:
        for i in mods[m]:
            if i in pos:
                if pos[i] >= pos[m]:
                    bad.append(f"{m} imports {i} listed later")
            elif not has_olean(i):
                bad.append(f"{m} imports {i}: not listed and no olean")
    os.makedirs(out, exist_ok=True)
    with open(os.path.join(out, "replay-order.txt"), "w") as fh:
        fh.write("\n".join(m.replace(".", "/") for m in order) + "\n")
    direct = sorted(m for m in closure if TARGET in mods[m])
    with open(os.path.join(out, "chains.txt"), "w") as fh:
        for d in direct:
            up, todo = set(), [d]
            while todo:
                m = todo.pop()
                if m in up or m not in closure:
                    continue
                up.add(m)
                todo.extend(mods[m])
            chain = [m for m in order if m in up]
            fh.write(d + ": " + " ".join(chain) + "\n")
    print(f"modules in the tree: {len(mods) - 1} (+ root TCSlib)")
    print(f"downstream closure of {TARGET}: {len(order)} modules (root TCSlib excluded)")
    print(f"direct importers ({len(direct)}): " + ", ".join(direct))
    print(f"root TCSlib in the list: {'TCSlib' in order}")
    if bad:
        print("FAIL: " + "; ".join(bad))
        sys.exit(1)
    print("every import of every listed module is listed earlier or present as an olean: PASS")


if __name__ == "__main__":
    main()
