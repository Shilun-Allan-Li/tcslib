"""Freeze check of the landing form of `Build/NDHost.lean` (read-only; standard library only).

Usage: python3 -I freeze_ndhost.py <tip NDHost.lean> <landed NDHost.lean> <unit.lean>

1. Code: strips every comment (nested block comments and docstrings, line comments) and blank
   line from the three files. The landed code must be exactly the tip's code with one line
   `import TCSlib.Complexity.TuringMachine.Build.Catalog` after its last import, followed by the
   code of the unit's part (everything after the unit's last `-- @imports` line).
2. Text: the tip's text from the end of its module docstring to its end (every existing
   declaration with its docstring, byte for byte) must occur verbatim in the landed file, and
   the unit's part body must be the landed file's suffix.
3. Declarations: the tip's declarations, by name, and the landed file's.
Exit status 0 iff all three hold.
"""
import re
import sys


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
    lines = [l.split("--")[0].rstrip() for l in "".join(out).splitlines()]
    return [l for l in lines if l.strip()]


DECL = re.compile(r"^(?:private\s+)?(theorem|lemma|def|structure|abbrev|inductive|instance)\s+(\S+)")
a_raw = open(sys.argv[1], encoding="utf-8").read()
b_raw = open(sys.argv[2], encoding="utf-8").read()
u_raw = open(sys.argv[3], encoding="utf-8").read()
ul = u_raw.split("\n")
last = max(i for i, l in enumerate(ul) if l.startswith("-- @imports "))
part = "\n".join(ul[last + 1:]).strip("\n") + "\n"
a, b, c = strip(a_raw), strip(b_raw), strip(part)
k = max(i for i, l in enumerate(a) if l.startswith("import "))
expect = a[:k + 1] + ["import TCSlib.Complexity.TuringMachine.Build.Catalog"] + a[k + 1:] + c
ok1 = b == expect
print(f"1. code lines: tip {len(a)}, part {len(c)}, landed {len(b)}; "
      f"landed = tip + 1 import + part: {ok1}")
doc_end = a_raw.index("-/\n", a_raw.index("/-!")) + 3
tail = a_raw[doc_end:]
ok2a = b_raw.count(tail.rstrip("\n") + "\n") == 1
ok2b = b_raw.endswith(part)
print(f"2. the tip's text after its module docstring ({tail.count(chr(10))} lines) occurs "
      f"verbatim once in the landed file: {ok2a}; part body is the landed suffix: {ok2b}")
da = [m.group(2) for l in a_raw.split("\n") if (m := DECL.match(l))]
db = [m.group(2) for l in b_raw.split("\n") if (m := DECL.match(l))]
print(f"3. declarations: tip {len(da)} {da}; landed {len(db)} (the tip's, in order, "
      f"first: {db[:len(da)] == da})")
ok = ok1 and ok2a and ok2b and db[:len(da)] == da
print("FREEZE OK" if ok else "FREEZE FAILED")
sys.exit(0 if ok else 1)
