"""Import graph and replay list of the dedup payback landing (read-only; git only as `rev-parse`).

Usage: python3 -I -B graph.py <base export> <L> --oleans <snapshot> --packages <worktree>

1. The base: the campaign tip (`git rev-parse`); its Lean files equal those of the snapshot's
   base `lib.SNAP_BASE` (asserted with `git diff --name-only`).
2. The replay list: the touched modules and their downstream closure in the landed import
   graph, topologically ordered (asserted), without the root `TCSlib` (asserted absent),
   written to <L>/replay-order.txt. Every header import of a listed module is listed or has an
   olean: a `TCSlib` import in the snapshot, any other import in the packages or the toolchain
   (asserted).
3. Overlap with the in-flight landings (MIG-1 stage S, C1-A round 2, G2-G4): touched files
   (asserted none) and replay-list members (reported).
4. The imports of every cut file are present in the snapshot (asserted).
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lib  # noqa: E402
import edits as E  # noqa: E402

T = "TCSlib.Complexity."
INFLIGHT = {
    "MIG-1 stage S": ["TuringMachine.Simulation", "TuringMachine.Composition",
                      "TuringMachine.Build.Wrappers", "TuringMachine.Encoding",
                      "ClassP.TimeConstructible", "TuringMachine.Build.Loop",
                      "TuringMachine.Build.Primitives", "TuringMachine.Build.Catalog"],
    "C1-A round 2": ["TuringMachine.Build.Embed", "SpaceComplexity.Inclusions",
                     "TuringMachine.Build.NDHost"],
    "G2-G4": ["TuringMachine.Build.Catalog", "TuringMachine.Build.Contract.Catalog",
              "TuringMachine.Build.Zone"],
}


def main():
    args = sys.argv[1:]
    OL = args[args.index("--oleans") + 1]
    PK = args[args.index("--packages") + 1]
    base, L = args[:2]
    tree = os.path.join(L, "tree")
    bc = lib.base_commit()
    live = lib.tip()
    moved = lib.lean_diff(bc, live)
    print(f"export {bc} (base-commit.txt); live tip {live}; Lean files the tip changed since the "
          f"base: {moved}")
    snap = lib.git("rev-parse", "--verify", lib.SNAP_BASE + "^{commit}").strip()
    dl = lib.lean_diff(snap, bc)
    print(f"the snapshot's base {snap} (the snapshot's commit, lib.SNAP_BASE): Lean "
          f"files differing from the export: {dl}")
    assert not dl
    g = lib.graph(base, overlay=tree)
    gb = lib.graph(base)
    print(f"graph: {len(g)} modules ({len(g) - 1} under TCSlib/ and the root `TCSlib`)")
    changed = [lib.mod_of_path(v[0]) for v in E.FILES.values()]
    for k, (rel, _, _) in E.FILES.items():
        m = lib.mod_of_path(rel)
        if g[m] != gb[m]:
            print(f"imports changed: {m}: +{[i for i in g[m] if i not in gb[m]]} "
                  f"-{[i for i in gb[m] if i not in g[m]]}")
    need = lib.down(g, changed)
    print(f"\n## Replay list\ntouched modules: {len(changed)}; downstream closure: {len(need)} "
          f"(root TCSlib in it: {'TCSlib' in need})")
    for m in changed:
        print(f"  {m[len(T):] if m.startswith(T) else m}: {len(lib.down(g, [m])) - 1} downstream")
    order = lib.topo(g, need - {"TCSlib"})
    pos = {m: i for i, m in enumerate(order)}
    assert all(pos[d] < pos[m] for m in order for d in g[m] if d in pos), "not topological"
    assert "TCSlib" not in order and len(set(order)) == len(order)
    assert set(order) == need - {"TCSlib"}
    lib.wr(os.path.join(L, "replay-order.txt"), "\n".join(lib.path_of_mod(m)[:-5] for m in order) + "\n")
    if moved:
        with_tip = {}
        import subprocess
        for rel in moved:
            p = subprocess.run(["git", "-C", lib.REPO, "show", f"{live}:{rel}"], capture_output=True,
                               text=True)
            with_tip[lib.mod_of_path(rel)] = [i for i in lib.header_imports(p.stdout)
                                              if i.startswith("TCSlib")] if p.returncode == 0 else None
        g2 = dict(g)
        for m, imps in with_tip.items():
            if imps is None:
                g2.pop(m, None)
            else:
                g2[m] = imps
        need2 = lib.down(g2, changed) - {"TCSlib"}
        mods = {lib.mod_of_path(r) for r in moved}
        print(f"at the live tip: the downstream closure of the touched modules is "
              f"{'the same' if need2 == need - {'TCSlib'} else 'DIFFERENT'} ({len(need2)} modules); "
              f"the tip's changed modules in it: {sorted(mods & need2)}; in the touched modules' "
              f"upstream closure: {sorted(m[len(T):] for m in mods & lib.up(g, changed))}")
    print(f"Replay list: {len(order)} modules ({len(changed)} touched, {len(order) - len(changed)} "
          f"downstream), topologically ordered (asserted), without the root TCSlib; written to "
          f"replay-order.txt")
    print("first:", order[:3], "... last:", order[-3:])
    pk = []
    for d in sorted(os.listdir(os.path.join(PK, ".lake", "packages"))):
        p = os.path.join(PK, ".lake", "packages", d, ".lake", "build", "lib", "lean")
        if os.path.isdir(p):
            pk.append(p)
    tc = lib.rd(os.path.join(base, "lean-toolchain")).strip()
    tcdir = os.path.join(os.path.expanduser("~"), ".elan", "toolchains",
                         tc.replace("/", "--").replace(":", "---"), "lib", "lean")
    if os.path.isdir(tcdir):
        pk.append(tcdir)

    def olean(rt, d):
        return os.path.isfile(os.path.join(rt, *d.split(".")) + ".olean")
    listed = set(order)
    cnt, missing = {"listed": 0, "snapshot": 0, "packages": 0}, []
    for m in order:
        p = os.path.join(tree, lib.path_of_mod(m))
        p = p if os.path.isfile(p) else os.path.join(base, lib.path_of_mod(m))
        for d in lib.header_imports(lib.rd(p)):
            if d in listed:
                cnt["listed"] += 1
            elif d.startswith("TCSlib"):
                cnt["snapshot"] += 1 if olean(OL, d) else 0
                if not olean(OL, d):
                    missing.append((m, d))
            elif any(olean(q, d) for q in pk):
                cnt["packages"] += 1
            else:
                missing.append((m, d))
    print(f"header imports of the listed modules: {cnt['listed']} listed, {cnt['snapshot']} TCSlib "
          f"with a snapshot olean, {cnt['packages']} package or toolchain oleans; neither: "
          f"{len(missing)} {missing[:5]}")
    assert not missing
    print("imports check: PASS")
    print("\n## In-flight landings")
    touched = {lib.mod_of_path(v[0]) for v in E.FILES.values()}
    for lab, ms in INFLIGHT.items():
        ms = [T + m for m in ms]
        for m in ms:
            assert m in g, m
        print(f"{lab}: touched by this landing: {sorted(touched & set(ms))}; on the replay list: "
              f"{sorted(x[len(T):] for x in set(ms) & listed)}")
        assert not touched & set(ms)
    print("\n## Cut imports")
    meta = json.loads(lib.rd(os.path.join(L, "work", "cut", "cuts.json")))
    bad = []
    for k, m in meta.items():
        for d in m["imports"]:
            if d.startswith("TCSlib") and not olean(OL, d):
                bad.append((k, d))
            elif not d.startswith("TCSlib") and not any(olean(q, d) for q in pk):
                bad.append((k, d))
    print(f"cut files: {len(meta)}; imports without an olean: {bad}")
    assert not bad
    print("cut imports check: PASS")


if __name__ == "__main__":
    main()
