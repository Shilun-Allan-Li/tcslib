"""Is the landing still valid at a campaign tip that moved past the base? (read-only)

Usage: python3 -I tipcheck.py <base root> <tip files root> <name-status file> <replay-order.txt>

<name-status file> is `git diff --name-status <base> <tip> -- '*.lean'`; <tip files root> holds
the tip's version of every added or modified file. The landing stays valid, with the evidence
taken at the base, when
  (a) `Diagonal.lean` itself is unchanged;
  (b) no changed module lies in `Diagonal`'s own import closure (so the standalone elaboration,
      the axioms, the freeze and the names screen are unaffected);
  (c) Diagonal's downstream closure, recomputed with the tip's imports, equals the replay list.
It also lists the changed modules that lie in the import closure of some replay module: the
cut checks were taken at the base, and the landing replay re-checks those modules at the tip.
Exit 1 if (a), (b) or (c) fails.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(__file__))
from graph import imports_of  # noqa: E402

TARGET = "TCSlib.Complexity.TimeHierarchy.Diagonal"


def mod(path):
    return path[:-5].replace("/", ".")


def main():
    base, tip, ns, replay_p = sys.argv[1:5]
    mods = {}
    for d, _, fs in os.walk(os.path.join(base, "TCSlib")):
        for f in fs:
            if f.endswith(".lean"):
                p = os.path.join(d, f)
                mods[mod(os.path.relpath(p, base))] = imports_of(p)
    changed = []
    for line in open(ns, encoding="utf-8"):
        if not line.strip():
            continue
        st, path = line.split()[0], line.split()[-1]
        if not path.startswith("TCSlib/"):
            continue
        m = mod(path)
        changed.append((st[0], m))
        if st[0] == "D":
            mods.pop(m, None)
        else:
            mods[m] = imports_of(os.path.join(tip, path))
    cset = {m for _, m in changed}
    ok = True
    print(f"changed Lean modules between the base and the tip: {len(changed)}")
    for st, m in changed:
        print(f"  {st} {m}")
    a = TARGET not in cset
    print(f"(a) Diagonal.lean unchanged: {a}")
    up, todo = set(), [TARGET]
    while todo:
        m = todo.pop()
        if m in up or m not in mods:
            continue
        up.add(m)
        todo.extend(mods[m])
    b = not (cset & up)
    print(f"(b) no changed module in Diagonal's own import closure ({len(up)} modules): {b}"
          + ("" if b else f" — {sorted(cset & up)}"))
    rev = {}
    for m, imps in mods.items():
        for i in imps:
            rev.setdefault(i, set()).add(m)
    down, todo = set(), [TARGET]
    while todo:
        m = todo.pop()
        if m in down:
            continue
        down.add(m)
        todo.extend(rev.get(m, ()))
    down.discard("TCSlib")
    replay = {l.strip().replace("/", ".") for l in open(replay_p) if l.strip()}
    c = down == replay
    print(f"(c) downstream closure at the tip equals replay-order.txt ({len(replay)} modules): {c}")
    upr, todo = set(), list(replay)
    while todo:
        m = todo.pop()
        if m in upr or m not in mods:
            continue
        upr.add(m)
        todo.extend(mods[m])
    inter = sorted(cset & upr)
    print(f"changed modules inside the replay modules' import closures (re-checked by the landing "
          f"replay at the tip; the cut checks are at the base): {inter if inter else 'none'}")
    ok = a and b and c
    print("TIP: PASS — the landing tree is valid at the tip" if ok else "TIP: FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
