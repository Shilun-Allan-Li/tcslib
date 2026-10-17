"""Name screen for the C1 assembly unit (read-only; standard library only).

Usage: python3 -I names_asm.py <unit.lean> <tip source tree> [--allow <path prefix>]...
                                [<pending unit or draft> ...]

Population (exactly): the unit's explicit declarations (`theorem|lemma|def|structure|abbrev|
inductive|instance` at line start, namespaces resolved, comments stripped), plus the names Lean
generates that a clash could hit: the derived instances `Turing.instDecidableEqGuessRunPhase`
and `Turing.instFintypeGuessRunPhase` (names read off `#check` in the axioms probe) and the
six constructors `Turing.GuessRunPhase.<c>`. Against:
1. every explicit declaration of the tip's `TCSlib` tree (full names), and every
   constructor of an `inductive` there (`Ns.T.c`, from `| c` lines directly after the header);
2. each pending unit or draft given (other gates' material, not landed), full names;
3. short names: a unit public name whose last component is also the last component of another
   TCSlib declaration (reported for review; not a clash by itself).
4. duplicates within the unit.
Exit status (round 2, finding m3): 1 if there is any full-name clash with the tree, any shared
name with a pending file that is not under an `--allow` prefix, or any duplicate; 0 otherwise.
An `--allow` prefix is a reviewed allowlist entry (for instance, the committed evidence of an
earlier round of this same gate, whose files declare the same names by construction); its
shared names are printed, marked ALLOWED, and do not count.
"""
import os
import re
import sys

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(private\s+)?(?:noncomputable\s+)?"
                  r"(theorem|lemma|def|structure|abbrev|inductive|instance|class|axiom)\s+"
                  r"([A-Za-z0-9_.'«»₀-₉]+)")
CTOR = re.compile(r"^\s*\|\s*([A-Za-z_][A-Za-z0-9_']*)")
GENERATED = ["Turing.instDecidableEqGuessRunPhase", "Turing.instFintypeGuessRunPhase"] + [
    f"Turing.GuessRunPhase.{c}" for c in ["pre", "guess", "skip", "back", "run", "out"]]


def strip(src):
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if src.startswith("-/", i) and depth > 0:
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(src[i])
        i += 1
    return "\n".join(l.split("--")[0] for l in "".join(out).splitlines())


def decls(path, ctors=False):
    ns, res, ind = [], [], None
    for line in strip(open(path, encoding="utf-8").read()).splitlines():
        s = line.strip()
        m = re.match(r"namespace\s+(\S+)", s)
        if m:
            ns.append(m.group(1))
            ind = None
            continue
        m = re.match(r"end\s+(\S+)", s)
        if m and ns and ns[-1] == m.group(1):
            ns.pop()
            ind = None
            continue
        m = DECL.match(s)
        if m:
            n = m.group(3)
            n = n[len("_root_."):] if n.startswith("_root_.") else ".".join(ns + [n])
            res.append((n, bool(m.group(1))))
            ind = n if m.group(2) == "inductive" else None
            continue
        if ctors and ind:
            c = CTOR.match(line)
            if c:
                res.append((ind + "." + c.group(1), False))
            elif s and not s.startswith("|") and not s.startswith("deriving"):
                ind = None
    return res


def main():
    unit, root, rest = sys.argv[1], sys.argv[2], sys.argv[3:]
    allow, pending, i = [], [], 0
    while i < len(rest):
        if rest[i] == "--allow":
            allow.append(rest[i + 1])
            i += 2
        else:
            pending.append(rest[i])
            i += 1
    gen = GENERATED if "inductive GuessRunPhase" in open(unit, encoding="utf-8").read() else []
    mine = decls(unit) + [(n, False) for n in gen]
    pub = [n for n, p in mine if not p]
    priv = [n for n, p in mine if p]
    print(f"{len(mine)} names in the population ({len(pub)} public, {len(priv)} private; "
          f"{len(gen)} generated)")
    theirs = {}
    nfiles = 0
    for d, _, fs in os.walk(os.path.join(root, "TCSlib")):
        for f in fs:
            if f.endswith(".lean"):
                nfiles += 1
                p = os.path.join(d, f)
                for n, _ in decls(p, ctors=True):
                    theirs.setdefault(n, []).append(os.path.relpath(p, root))
    print(f"   screened against {len(theirs)} names from {nfiles} TCSlib files")
    full = [(n, theirs[n]) for n, _ in mine if n in theirs]
    print(f"1. full-name clashes with the TCSlib tree: {len(full)}")
    for n, w in full:
        print("   CLASH", n, w)
    hits_total, hits_allowed = 0, 0
    for u in pending:
        names = {n for n, _ in decls(u, ctors=True)}
        hits = sorted(n for n, _ in mine if n in names)
        allowed = any(os.path.abspath(u).startswith(os.path.abspath(a)) for a in allow)
        if allowed:
            hits_allowed += len(hits)
        else:
            hits_total += len(hits)
        if hits:
            tag = "ALLOWED " if allowed else "CLASH "
            print(f"2. {tag}shared with {os.path.relpath(u, root)}: {len(hits)}: "
                  + ", ".join(hits[:6]) + (" …" if len(hits) > 6 else ""))
    print(f"2. pending units/drafts screened: {len(pending)}; shared names counted: {hits_total}; "
          f"allowed (under {len(allow)} reviewed prefixes): {hits_allowed}")
    short = {}
    for n in theirs:
        short.setdefault(n.split(".")[-1], set()).add(n)
    amb = []
    for n in pub:
        others = sorted(m for m in short.get(n.split(".")[-1], ()) if m != n)
        if others:
            amb.append((n, others))
    print(f"3. unit public names whose last component also names another TCSlib declaration: "
          f"{len(amb)}")
    for n, o in amb:
        print("   SHORT", n, "~", ", ".join(o[:4]) + (f" … ({len(o)})" if len(o) > 4 else ""))
    dup = sorted({n for n, _ in mine if [m for m, _ in mine].count(n) > 1})
    print("4. duplicates within the unit:", dup)
    sys.exit(1 if full or dup or hits_total else 0)


if __name__ == "__main__":
    main()
