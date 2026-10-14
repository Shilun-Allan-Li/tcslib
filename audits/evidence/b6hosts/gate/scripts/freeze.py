"""Freeze check for patched existing files (read-only; standard library only).

Usage: python3 -I freeze.py [--report] <original.lean> <patched.lean>
       [allowed-statement-changes] [allowed-body-changes]

Each file is cut into declarations (with their namespaces). For every declaration the
docstring, the statement (the comment-stripped text after the declared name up to the proof's
`:=`, a ` where`, or the first match arm; a `:=` on a line with `let` or `have` belongs to the
statement) and the body (the comment-stripped rest) are compared, whitespace-collapsed.
Reports: declarations added and removed (public and private separately), and for each kept
declaration whether its statement, body or docstring changed. A statement or body change not
listed in the allowance arguments (comma-separated full names) is flagged UNAUTHORIZED; the
exit status is 1 if anything is flagged. The module docstring and other comments outside
declarations are reported as one item.
"""
import re
import sys

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*((?:(?:private|protected|noncomputable|nonrec|partial)\s+)*)"
                  r"(theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s(:{\[]+)?")
STOP = re.compile(r"^(end\b|namespace\b|section\b|open\b|variable\b|set_option\b|#|attribute\b|"
                  r"universe\b|noncomputable section\b)")


def split_comments(src):
    """Return (code with comments blanked, list of (start, end, text, is_doc) comments)."""
    out, comments, i, n = [], [], 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/-", j):
                    depth += 1; j += 2
                elif src.startswith("-/", j):
                    depth -= 1; j += 2
                else:
                    j += 1
            comments.append((i, j, src[i:j], src.startswith("/--", i)))
            out.append("".join(c if c == "\n" else " " for c in src[i:j]))
            i = j
        elif src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        else:
            out.append(src[i]); i += 1
    return "".join(out), comments


def decls(src):
    code, comments = split_comments(src)
    lines = code.split("\n")
    offs, o = [], 0
    for l in lines:
        offs.append(o); o += len(l) + 1
    docs = {c[1]: c[2] for c in comments if c[3]}
    stack, res, cur = [], [], None

    def close(endline):
        nonlocal cur
        if cur:
            text = "\n".join(lines[cur["line"]:endline])
            res.append(dict(cur, text=text))
        cur = None

    for i, l in enumerate(lines):
        m = DECL.match(l)
        if m and not l.startswith(" "):
            close(i)
            name = m.group(3) or "<anon>"
            full = name[len("_root_."):] if name.startswith("_root_.") else \
                ".".join([s for k, s in stack if k == "ns"] + [name])
            # the docstring that ends right before this line
            doc = ""
            for (a, b, t, isdoc) in comments:
                if isdoc and b <= offs[i] and not src[b:offs[i]].strip():
                    doc = t
            cur = {"name": full, "private": "private" in m.group(1), "line": i, "doc": doc}
            continue
        s = l.strip()
        if STOP.match(l):
            close(i)
            mm = re.match(r"^namespace\s+(\S+)", l)
            if mm:
                for part in mm.group(1).split("."):
                    stack.append(("ns", part))
            mm = re.match(r"^(?:noncomputable\s+)?section\b\s*(\S*)", l)
            if mm:
                stack.append(("sec", mm.group(1)))
            mm = re.match(r"^end\b\s*(\S*)", l)
            if mm:
                nm = mm.group(1)
                if nm:
                    for part in reversed(nm.split(".")):
                        if stack and stack[-1][1] == part:
                            stack.pop()
                elif stack and stack[-1][0] == "sec":
                    stack.pop()
    close(len(lines))
    out = {}
    for d in res:
        t = d["text"]
        hm = DECL.match(t)  # drop the keyword and the declared name: compare from the binders on
        t = t[hm.end():] if hm else t
        mm = None
        for cand in re.finditer(r":=|\swhere\b|\n\s*\|", t):
            line = t[t.rfind("\n", 0, cand.start()) + 1:cand.start()]
            if cand.group(0) == ":=" and re.search(r"\b(let|have)\b", line):
                continue  # a `let`/`have` inside the statement, not the proof's `:=`
            mm = cand
            break
        stmt, body = (t[:mm.start()], t[mm.start():]) if mm else (t, "")
        key = d["name"]
        while key in out:
            key += "'"
        out[key] = {"private": d["private"], "stmt": " ".join(stmt.split()),
                    "body": " ".join(body.split()), "doc": " ".join(d["doc"].split())}
    return out, " ".join(" ".join(c[2] for c in comments if not c[3]).split())


def main():
    report = "--report" in sys.argv
    if report:
        sys.argv.remove("--report")
    a_src, b_src = open(sys.argv[1], encoding="utf-8").read(), open(sys.argv[2],
                                                                     encoding="utf-8").read()
    allow_stmt = set(sys.argv[3].split(",")) if len(sys.argv) > 3 and sys.argv[3] else set()
    allow_body = set(sys.argv[4].split(",")) if len(sys.argv) > 4 and sys.argv[4] else set()
    A, ca = decls(a_src)
    B, cb = decls(b_src)
    bad = 0
    pubA = {n for n in A if not A[n]["private"]}
    pubB = {n for n in B if not B[n]["private"]}
    privA, privB = set(A) - pubA, set(B) - pubB
    print(f"declarations before/after: {len(A)}/{len(B)} (public {len(pubA)}/{len(pubB)}, "
          f"private {len(privA)}/{len(privB)})")
    print("public added:", sorted(pubB - pubA))
    print("public removed:", sorted(pubA - pubB))
    print("private added:", sorted(privB - privA))
    print("private removed:", sorted(privA - privB))
    for n in sorted(set(A) & set(B)):
        a, b = A[n], B[n]
        flags = []
        if a["stmt"] != b["stmt"]:
            ok = n in allow_stmt
            flags.append("statement changed" + (" (authorized)" if ok else " UNAUTHORIZED"))
            bad += not ok
        if a["body"] != b["body"]:
            ok = n in allow_body
            flags.append("body changed" + (" (authorized)" if ok else " UNAUTHORIZED"))
            bad += not ok
        if a["doc"] != b["doc"]:
            flags.append("docstring changed")
        if a["private"] != b["private"]:
            flags.append("visibility changed UNAUTHORIZED")
            bad += 1
        if flags:
            print(f"  {n}{' (private)' if a['private'] else ''}: " + "; ".join(flags))
    unchanged = sum(1 for n in set(A) & set(B) if A[n] == B[n])
    print(f"kept declarations byte-identical (comment-stripped statement, body, docstring): "
          f"{unchanged} of {len(set(A) & set(B))}")
    print("other comments (module docstring, section headers):",
          "unchanged" if ca == cb else "changed")
    for n in allow_stmt | allow_body:
        if n and n not in A:
            print(f"  allowance names an unknown declaration: {n}")
            bad += 1
    if report:
        print(f"RESULT: comparison only; {bad} difference(s) outside the allowances")
        return
    print("RESULT:", "PASS" if bad == 0 else f"FAIL ({bad})")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
