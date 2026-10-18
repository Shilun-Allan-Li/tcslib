"""Declaration-level freeze of an edited file (read-only; standard library only).

Usage: python3 -I freeze.py <old.lean> <new.lean>

For every declaration of <old>: its statement (text up to the top-level `:=`/`where`, comments
stripped, whitespace collapsed; `sigdiff.statement`) and its whole comment-stripped text are
compared with the declaration of the same name in <new>. Reported: statement changes (none are
expected), body-only changes (each listed), removals and additions. Comments and docstrings are
not compared (a docstring-only change is reported separately, by name).
"""
import os
import re
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sigdiff import DECL, statement, strip  # noqa: E402


def decls(path, keep_comments=False):
    raw = open(path, encoding="utf-8").read()
    src = raw if keep_comments else strip(raw)
    lines = src.split("\n")
    ns, starts = [], []
    for idx, line in enumerate(lines):
        s = line.strip()
        m = re.match(r"namespace\s+(\S+)", s)
        if m:
            ns.append(m.group(1))
        m2 = re.match(r"end\s+(\S+)", s)
        if m2 and ns and ns[-1] == m2.group(1):
            ns.pop()
        m3 = DECL.match(s)
        if m3:
            n = m3.group(2)
            n = n[len("_root_."):] if n.startswith("_root_.") else ".".join(ns + [n])
            starts.append((idx, n))
    res = {}
    stop = re.compile(r"^(end|namespace|section|variable|open|set_option)\b")
    for k, (idx, n) in enumerate(starts):
        end = starts[k + 1][0] if k + 1 < len(starts) else len(lines)
        for i in range(idx + 1, end):
            if stop.match(lines[i]):
                end = i
                break
        res[n] = "\n".join(lines[idx:end])
    return res


show = "--show" in sys.argv
old, new = decls(sys.argv[1]), decls(sys.argv[2])
same = stmt = body = 0
for n, t in old.items():
    if n not in new:
        print(f"REMOVED    {n}")
        continue
    t2 = new[n]
    s1, s2 = " ".join(statement(t).split()), " ".join(statement(t2).split())
    if s1 != s2:
        stmt += 1
        print(f"STATEMENT  {n}\n   old: {s1}\n   new: {s2}")
    elif " ".join(t.split()) != " ".join(t2.split()):
        body += 1
        print(f"BODY       {n}")
        if show:
            import difflib
            for l in difflib.unified_diff([x for x in t.split("\n") if x.strip()],
                                          [x for x in t2.split("\n") if x.strip()],
                                          lineterm="", n=0):
                if not l.startswith(("---", "+++")):
                    print("    " + l)
    else:
        same += 1
added = [n for n in new if n not in old]
print(f"{len(old)} old declarations: identical {same}, statement changed {stmt}, body changed "
      f"{body}, removed {len([n for n in old if n not in new])}; added {len(added)}"
      + (": " + ", ".join(added) if added else ""))
