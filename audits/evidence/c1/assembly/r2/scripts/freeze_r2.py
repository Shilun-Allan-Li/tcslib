"""Statement and code freeze of the round-2 landing edits (read-only; standard library only).

Usage: python3 -I freeze_r2.py <tip file> <landed file> <label> [<allowed changed decl> ...]

Both files are stripped of comments (nested block comments, docstrings, line comments) and
split into declarations (`theorem|lemma|def|abbrev|instance|inductive|structure|class` at line
start, optionally `private`/`noncomputable`/attributes; full names resolved through
`namespace` lines). For each declaration the *statement* is its text up to the first `:=` at
bracket depth 0 (the whole block when there is none), whitespace-normalized; the *code* is its
whole block. Checks, each printed:
1. every tip declaration is in the landed file with an identical statement (public and private);
2. the landed file adds only new names (listed), removes none;
3. the code of every tip declaration is identical, except the declarations named on the command
   line (whose changed code is printed as a diff);
4. the code outside declarations (imports, options, namespace lines) differs only by added lines.
Exit status 0 iff 1-4 hold.
"""
import difflib
import re
import sys

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(private\s+)?(?:noncomputable\s+)?(?:protected\s+)?"
                  r"(theorem|lemma|def|abbrev|instance|inductive|structure|class)\s+"
                  r"([A-Za-z0-9_.'«»₀-₉]+)")


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
    return [l.split("--")[0].rstrip() for l in "".join(out).splitlines()]


def statement(block):
    text, depth = "\n".join(block), 0
    for k, ch in enumerate(text):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == ":" and depth == 0 and text[k:k + 2] == ":=":
            return " ".join(text[:k].split())
    return " ".join(text.split())


def decls(path):
    lines = strip(open(path, encoding="utf-8").read())
    ns, res, other, cur = [], {}, [], None
    for l in lines:
        s = l.strip()
        m = DECL.match(l)
        if m:
            n = m.group(3)
            n = n[len("_root_."):] if n.startswith("_root_.") else ".".join(ns + [n])
            cur = [n, bool(m.group(1)), [l]]
            assert n not in res, f"duplicate {n} in {path}"
            res[n] = cur
            continue
        mns = re.match(r"namespace\s+(\S+)", s)
        mend = re.match(r"end\s+(\S+)", s)
        if l and not l[0].isspace() and (mns or mend or s.startswith(("section", "open", "variable",
                                                                          "import", "set_option"))):
            cur = None
            if mns:
                ns.append(mns.group(1))
            elif mend and ns and ns[-1] == mend.group(1):
                ns.pop()
            other.append(l)
            continue
        if cur is not None:
            if l.strip():
                cur[2].append(l)
        elif l.strip():
            other.append(l)
    return res, other


def main():
    tip, landed, label, allowed = sys.argv[1], sys.argv[2], sys.argv[3], set(sys.argv[4:])
    a, oa = decls(tip)
    b, ob = decls(landed)
    ok = True
    same = [n for n in a if n in b and statement(a[n][2]) == statement(b[n][2])]
    changed = [n for n in a if n in b and statement(a[n][2]) != statement(b[n][2])]
    removed = [n for n in a if n not in b]
    added = [n for n in b if n not in a]
    pub_a = sum(1 for n in a if not a[n][1])
    print(f"[{label}] tip declarations {len(a)} ({pub_a} public); landed {len(b)}")
    print(f"1. statements identical: {len(same)} of {len(a)}; changed: {changed}")
    print(f"2. removed: {removed}; added ({len(added)}): "
          + ", ".join(("private " if b[n][1] else "") + n for n in added))
    code_changed = [n for n in a if n in b and a[n][2] != b[n][2]]
    print(f"3. declarations whose code changed: {code_changed} (allowed: {sorted(allowed)})")
    for n in code_changed:
        if n in allowed:
            d = difflib.unified_diff(a[n][2], b[n][2], lineterm="", n=0)
            print("\n".join("   " + x for x in list(d)[2:]))
    extra = [l for l in ob if l not in oa]
    gone = [l for l in oa if l not in ob]
    print(f"4. lines outside declarations: added {extra}; removed {gone}")
    ok = not changed and not removed and set(code_changed) <= allowed and not gone
    print(f"[{label}] FREEZE {'OK' if ok else 'FAILED'}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
