"""Freeze check and public API delta of the dedup payback landing (read-only; stdlib only).
Fails closed.

Usage: python3 -I -B freeze.py <base export> <tree> [--override <key>=<path>]... [--json <out>]

The declaration cutter is the B6 gate's (`audits/evidence/b6hosts/gate/scripts/freeze.py`,
run from the base export unchanged): namespaced names, comment-stripped statement (up to the
proof's `:=`, a ` where` or the first match arm) and body, docstring separately, all
whitespace-collapsed. For each touched file the base is compared with the landed file, and
every difference must be authorized by edits.py:
* **statements** of kept declarations: unchanged, or exactly D1's rewrite of the base
  statement (`InWin N ` -> `Cfg.InWindow `; in ConfigGraph `InWindow s ` -> `Cfg.InWindow s `),
  in a D1 file only (allowance (a));
* **bodies**: unchanged, exactly D1's rewrite (a definition's body, or a proof that changes by
  the rewrite alone), or listed in BODY (proof changes and re-points);
* **visibility**: private -> public exactly for PROMOTED (allowance (b)); never public ->
  private;
* **added** declarations: exactly ADDED, all public (new shared lemmas and moved-in ones);
* **removed** declarations: exactly DELETED (allowance (c)); the 45 `b4m*` declarations of
  TQBF.lean are counted from the base's appendix and must all be private;
* **moves** (MOVES): the moved-in declaration's statement and body equal the deleted one's;
* **docstrings**: changed exactly for DOC; **other comments** exactly for MODDOC;
* **imports**: changed exactly as IMPORTS;
* every other public statement is byte-identical modulo whitespace.
An allowance that is not used FAILS too. The tree must hold exactly the touched files.
Prints the public API delta per file; exit 1 on any FAIL.
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lib  # noqa: E402
import edits as E  # noqa: E402


def d1(key, s):
    if key == "ConfigGraph":
        s = re.sub(r"(?<![A-Za-z0-9_.'])InWindow s ", "Cfg.InWindow s ", s + " ")[:-1]
    return re.sub(r"(?<![A-Za-z0-9_.'])InWin N ", "Cfg.InWindow ", s + " ")[:-1]


def resplit(d):
    """The B6 cutter ends a statement at its first `:=`, which for a named argument such as
    `ValidChk (N := N) …` is inside the statement. Such a statement is extended to the proof's
    `:= by` (or, for a definition, to its end)."""
    s, b = d["stmt"], d["body"]
    if re.search(r"\(\w+$", s) and b.startswith(":="):
        i = b.find(" := by")
        i = len(b) if i < 0 else i
        return dict(d, stmt=s + " " + b[:i], body=b[i:].strip())
    return d


def main():
    args = sys.argv[1:]
    over, jout = {}, None
    while "--override" in args:
        k = args.index("--override"); a, b = args[k + 1].split("=", 1); over[a] = b
        args = args[:k] + args[k + 2:]
    if "--json" in args:
        k = args.index("--json"); jout = args[k + 1]; args = args[:k] + args[k + 2:]
    base, tree = args[:2]
    bad, delta, decls = [], {}, {}
    for key, (rel, _, _) in E.FILES.items():
        a_src = lib.rd(os.path.join(base, rel))
        b_src = lib.rd(over.get(key, os.path.join(tree, rel)))
        A, ca = lib.declcut.decls(a_src)
        B, cb = lib.declcut.decls(b_src)
        A = {n: resplit(d) for n, d in A.items()}
        B = {n: resplit(d) for n, d in B.items()}
        decls[key] = (A, B)
        fails = []
        print(f"## {key} ({rel})")
        pubA = {n for n in A if not A[n]["private"]}
        pubB = {n for n in B if not B[n]["private"]}
        print(f"declarations before/after: {len(A)}/{len(B)} (public {len(pubA)}/{len(pubB)})")
        deleted = {n for n, _ in E.DELETED.get(key, set())}
        if key == "TQBF":
            b4m = {n for n in A if n.startswith("Complexity.b4m")}
            assert len(b4m) == 45 and all(A[n]["private"] for n in b4m), len(b4m)
            deleted |= b4m
        removed = set(A) - set(B)
        if removed != deleted:
            fails.append(f"removed {sorted(removed - deleted)}, not removed {sorted(deleted - removed)}")
        rem_pub = sorted(n for n in removed if not A[n]["private"])
        rem_priv = sorted(n for n in removed if A[n]["private"])
        print(f"public removed ({len(rem_pub)}): {rem_pub}")
        print(f"private removed ({len(rem_priv)}): "
              f"{rem_priv if len(rem_priv) < 20 else str(len(rem_priv)) + ' (b4m* and codec_core_window)'}")
        added = set(B) - set(A)
        want_add = E.ADDED.get(key, set())
        if added != want_add:
            fails.append(f"added {sorted(added - want_add)}, missing {sorted(want_add - added)}")
        if any(B[n]["private"] for n in added):
            fails.append(f"private additions {sorted(n for n in added if B[n]['private'])}")
        print(f"public added ({len(added)}): {sorted(added)}")
        promoted = {n for n in set(A) & set(B) if A[n]["private"] and not B[n]["private"]}
        demoted = {n for n in set(A) & set(B) if not A[n]["private"] and B[n]["private"]}
        if promoted != E.PROMOTED.get(key, set()):
            fails.append(f"visibility {sorted(promoted ^ E.PROMOTED.get(key, set()))}")
        if demoted:
            fails.append(f"made private {sorted(demoted)}")
        print(f"made public in place ({len(promoted)}): {sorted(promoted)}")
        restated, d1body, bodies, docs = [], [], set(), set()
        for n in sorted(set(A) & set(B)):
            a, b = A[n], B[n]
            if a["stmt"] != b["stmt"]:
                if key in E.D1_FILES and d1(key, a["stmt"]) == b["stmt"]:
                    restated.append(n)
                else:
                    fails.append(f"statement changed {n}")
                    print(f"  {n}: statement changed, not D1's rewrite  FAIL")
            if a["body"] != b["body"]:
                if key in E.D1_FILES and d1(key, a["body"]) == b["body"]:
                    d1body.append(n)
                elif n in E.BODY.get(key, set()):
                    bodies.add(n)
                else:
                    fails.append(f"body changed {n}")
                    print(f"  {n}: body changed  FAIL")
            if a["doc"] != b["doc"]:
                docs.add(n)
        unused = E.BODY.get(key, set()) - bodies
        if unused:
            fails.append(f"unused body allowances {sorted(unused)}")
        if docs != E.DOC.get(key, set()):
            fails.append(f"docstrings changed {sorted(docs ^ E.DOC.get(key, set()))}")
        pub_restated = [n for n in restated if not B[n]["private"]]
        print(f"D1 restatements ({len(restated)}, public {len(pub_restated)}): {restated}")
        print(f"D1 rewrite of a body alone ({len(d1body)}): {d1body}")
        print(f"bodies changed by the edits ({len(bodies)}): {sorted(bodies)}")
        print(f"docstrings changed ({len(docs)}): {sorted(docs)}")
        if (ca != cb) != (key in E.MODDOC):
            fails.append("other comments " + ("changed" if ca != cb else "unchanged"))
        print("other comments (module docstring, section headers):",
              "changed" if ca != cb else "unchanged")
        ia, ib = lib.header_imports(a_src), lib.header_imports(b_src)
        new_imp = [i for i in ib if i not in ia]
        if [i for i in ia if i not in ib] or new_imp != E.IMPORTS.get(key, []):
            fails.append(f"imports {ia} -> {ib}")
        print(f"imports added: {new_imp}")
        same = sum(1 for n in set(A) & set(B) if A[n]["stmt"] == B[n]["stmt"]
                   and not A[n]["private"])
        print(f"public statements kept byte-identical (whitespace-collapsed): {same} of "
              f"{len(pubA & pubB)}")
        delta[key] = {"public_removed": rem_pub, "private_removed": len(rem_priv),
                      "public_added": sorted(added), "promoted": sorted(promoted),
                      "public_restated": pub_restated, "restated_private":
                      [n for n in restated if B[n]["private"]],
                      "proofs_changed": sorted(bodies), "d1_bodies": d1body}
        print("RESULT:", "PASS" if not fails else f"FAIL ({'; '.join(fails)})")
        bad += [f"{key}: {x}" for x in fails]
    for new, (k, old) in E.MOVES.items():
        tk = next(x for x, v in E.ADDED.items() if new in v)
        Bn = decls[tk][1].get(new)
        Ao = decls[k][0].get(old)
        ok = Bn is not None and Ao is not None and Bn["stmt"] == Ao["stmt"] and Bn["body"] == Ao["body"]
        print(f"move {old} ({k}) -> {new} ({tk}): statement and body kept: {ok}")
        if not ok:
            bad.append(f"move {new}")
    extra = []
    for dp, _, fs in os.walk(tree):
        for f in fs:
            r = os.path.relpath(os.path.join(dp, f), tree)
            if r not in {v[0] for v in E.FILES.values()}:
                extra.append(r)
    print(f"files in the tree other than the {len(E.FILES)} touched files: {extra}")
    if extra:
        bad.append(f"extra files {extra}")
    if jout:
        lib.wr(jout, json.dumps(delta, indent=1) + "\n")
    print("OVERALL:", "PASS" if not bad else f"FAIL ({len(bad)})")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
