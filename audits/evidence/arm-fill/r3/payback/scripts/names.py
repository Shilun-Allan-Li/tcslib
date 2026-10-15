"""Name screen of the dedup payback landing (read-only; standard library only).

Usage: python3 -I -B names.py <base export> <L> <packages worktree> [--extra <file.lean>]

1. **Clashes.** The new public names (ADDED and PROMOTED of edits.py) against every declaration
   of `TCSlib` at the base (public or private; the declaration cutter of the B6 gate) and of
   the packages' sources that mention `Turing` or `Complexity` (the B6 gate's lister, executed
   unchanged from the base export). The only allowed coincidence is a promotion's own private
   original. Anything else is a CLASH.
2. **Stale uses of deleted declarations.** Every deleted declaration (DELETED, and TQBF's 45
   `b4m*`) is looked up by its last component in the code (comments blanked) of every Lean file
   of the landed tree (the touched files landed, every other file at the base). A hit is
   accounted for only by a surviving declaration with the same last component (a moved copy,
   a promoted original, or an unrelated homonym, all listed); otherwise it is a STALE use.
3. **The new import** (VWord's `TCSlib.Programs.Util.List`): no declaration of its closure has
   the full name of a declaration downstream of VWord, and no file downstream of VWord opens
   `List`.
4. **Privates of other files**: no lemma-style identifier (one with an underscore; short
   binder names such as `T` or `test` are not names of declarations here) on an added line of a
   patch is the last component of another file's private declaration without a public
   declaration of that name.
5. Last-component screen (information): other declarations of the landed tree under `Turing`,
   `Complexity` or `BoolCircuit` with a new public name's last component.
With --extra, that file's declarations count as new names and its code is screened for stale
uses (the controls).
"""
import os
import re
import sys
import types

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lib  # noqa: E402
import edits as E  # noqa: E402

OPEN_NS = {"Turing", "Complexity", "Turing.NDTM", "Turing.FinNDTM", "Turing.Cfg",
           "Complexity.LogProg", "Complexity.Codec", "Complexity.QBF", "BoolCircuit.DAGCircuit"}


def all_files(base, tree):
    out = {}
    for dp, _, fs in os.walk(os.path.join(base, "TCSlib")):
        for f in fs:
            if f.endswith(".lean"):
                rel = os.path.relpath(os.path.join(dp, f), base)
                p = os.path.join(tree, rel)
                out[rel] = lib.rd(p if os.path.isfile(p) else os.path.join(base, rel))
    return out


def main():
    args = sys.argv[1:]
    extra = None
    if "--extra" in args:
        k = args.index("--extra"); extra = args[k + 1]; args = args[:k] + args[k + 2:]
    base, L, WT = args[:3]
    tree = os.path.join(L, "tree")
    b6path = os.path.join(base, "audits/evidence/b6hosts/gate/scripts/names.py")
    b6 = types.ModuleType("b6names")
    exec(compile(lib.rd(b6path), b6path, "exec"), b6.__dict__)
    fails = []
    new = {}
    for k, ns in E.ADDED.items():
        for n in ns:
            new[n] = (k, "added")
    for k, ns in E.PROMOTED.items():
        for n in ns:
            new[n] = (k, "promoted")
    if extra:
        D, _ = lib.declcut.decls(lib.rd(extra))
        for n in D:
            new[n] = ("extra", "control")
    # base declarations
    theirs = {}
    base_src = {}
    for dp, _, fs in os.walk(os.path.join(base, "TCSlib")):
        for f in fs:
            if f.endswith(".lean"):
                rel = os.path.relpath(os.path.join(dp, f), base)
                base_src[rel] = lib.rd(os.path.join(dp, f))
                D, _ = lib.declcut.decls(base_src[rel])
                for n, d in D.items():
                    theirs.setdefault(n.rstrip("'"), []).append((rel, d["private"]))
    npk = 0
    pk = os.path.join(WT, ".lake", "packages")
    for d in sorted(os.listdir(pk)):
        for dp, dirs, fs in os.walk(os.path.join(pk, d)):
            dirs[:] = [x for x in dirs if x != ".lake"]
            for f in fs:
                if f.endswith(".lean"):
                    p = os.path.join(dp, f)
                    s = lib.rd(p)
                    if "Turing" not in s and "Complexity" not in s:
                        continue
                    npk += 1
                    for n in b6.decls(p):
                        theirs.setdefault(n, []).append((os.path.relpath(p, pk), None))
    print(f"new public names: {len(new)} ({sum(1 for v in new.values() if v[1] == 'added')} added, "
          f"{sum(1 for v in new.values() if v[1] == 'promoted')} promoted in place"
          f"{', ' + str(sum(1 for v in new.values() if v[1] == 'control')) + ' control' if extra else ''})")
    print(f"screened against {len(theirs)} declaration names: TCSlib at the base and {npk} package "
          f"source files that mention Turing or Complexity")
    print("\n## 1. Full-name clashes")
    nclash = 0
    for n, (k, kind) in sorted(new.items()):
        for rel, priv in theirs.get(n, []):
            if kind == "promoted" and rel == E.FILES[k][0] and priv:
                continue
            print(f"  CLASH {n} ({k}, {kind}) with {'private ' if priv else ''}declaration in {rel}")
            nclash += 1
    print(f"clashes: {nclash}")
    if nclash:
        fails.append("clash")
    print("\n## 2. Stale uses of deleted declarations")
    files = all_files(base, tree)
    if extra:
        files["<extra>"] = lib.rd(extra)
    surviving = {}
    for rel, src in files.items():
        if rel == "<extra>":
            continue
        D, _ = lib.declcut.decls(src)
        for n in D:
            surviving.setdefault(n.rstrip("'").split(".")[-1], set()).add(n.rstrip("'"))
    deleted = []
    for k, s in E.DELETED.items():
        deleted += [(n, k, why) for n, why in s]
    D, _ = lib.declcut.decls(base_src[E.FILES["TQBF"][0]])
    deleted += [(n, "TQBF", "D6: the dead b4m appendix") for n in D if n.startswith("Complexity.b4m")]
    codes = {rel: lib.blank_comments(src) for rel, src in files.items()}
    nstale, homonyms = 0, []
    for n, k, why in sorted(deleted):
        short = n.split(".")[-1]
        hits = [(rel, c) for rel, code in codes.items() if (c := lib.token_count(code, short))]
        surv = sorted(surviving.get(short, set()) - {n})
        if hits and not surv:
            for rel, c in hits:
                print(f"  STALE {n} ({k}; {why}): {c} code token(s) `{short}` in {rel}")
                nstale += 1
        elif hits:
            homonyms.append((n, sum(c for _, c in hits), len(hits), surv))
    print(f"deleted declarations screened: {len(deleted)}; stale uses: {nstale}")
    print("deleted names whose last component survives (uses resolve to the survivor):")
    for n, c, f, surv in homonyms:
        print(f"  {n}: {c} code token(s) in {f} file(s); survivors {surv}")
    if nstale:
        fails.append("stale")
    print("\n## 3. The new import of Machines/VWord")
    g = lib.graph(base, overlay=tree)
    vw = lib.mod_of_path(E.FILES["VWord"][0])
    dn = lib.down(g, [vw])
    src_mods = lib.up(g, ["TCSlib.Programs.Util.List"])
    imp_names = {}
    for m in src_mods:
        Dm, _ = lib.declcut.decls(files[lib.path_of_mod(m)])
        for n in Dm:
            imp_names[n.rstrip("'")] = m
    clash3, opens = [], []
    for m in sorted(dn):
        rel = lib.path_of_mod(m)
        if rel not in files:
            continue
        Dm, _ = lib.declcut.decls(files[rel])
        clash3 += [(n, m, imp_names[n.rstrip("'")]) for n in Dm if n.rstrip("'") in imp_names]
        if re.search(r"^\s*open\b[^\n]*\bList\b|^\s*namespace\s+List\b", codes[rel], re.M):
            opens.append(m)
    print(f"closure of TCSlib.Programs.Util.List: {sorted(src_mods)}; modules downstream of VWord: "
          f"{len(dn)}; full-name clashes {clash3}; downstream files opening List: {opens}")
    if clash3 or opens:
        fails.append("import")
    print("\n## 4. Added lines referring to other files' private declarations")
    priv_short, pub_short = {}, set()
    for rel, src in files.items():
        if rel == "<extra>":
            continue
        Dm, _ = lib.declcut.decls(src)
        for n, d in Dm.items():
            (priv_short.setdefault(n.split(".")[-1], set()).add(rel) if d["private"]
             else pub_short.add(n.rstrip("'").split(".")[-1]))
    refs = []
    for key, (rel, _, _) in E.FILES.items():
        p = os.path.join(L, "patches", key + ".patch")
        if not os.path.isfile(p):
            continue
        added = "\n".join(l[1:] for l in lib.rd(p).split("\n") if l.startswith("+")
                          and not l.startswith("+++"))
        for m in lib.IDENT.finditer(lib.blank_comments(added)):
            for part in m.group(0).split("."):
                if ("_" in part and part in priv_short and part not in pub_short
                        and rel not in priv_short[part]):
                    refs.append((key, part, sorted(priv_short[part])))
    print(f"references: {sorted(set((a, b) for a, b, _ in refs))}")
    if refs:
        fails.append("private refs")
    print("\n## 5. Same last component elsewhere under Turing / Complexity (information)")
    last = {}
    for short, ns in surviving.items():
        last.setdefault(short, []).extend(ns)
    for n, (k, kind) in sorted(new.items()):
        c, ns = n.split(".")[-1], ".".join(n.split(".")[:-1])
        others = sorted(o for o in set(last.get(c, [])) if o != n and
                        (o.startswith("Turing.") or o.startswith("Complexity.") or o.startswith("BoolCircuit")))
        if others:
            flag = [o for o in others if ".".join(o.split(".")[:-1]) in OPEN_NS]
            print(f"  {n} ~ {others}{'  (in an opened namespace: ' + str(flag) + ')' if flag else ''}")
    print("\nRESULT:", "PASS" if not fails else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
