"""Compare each importer's baseline elaboration (base file against the snapshot) with its cut
check (against the landed Diagonal.lean). Read-only; standard library only.

Usage: python3 -I compare.py <out dir> <name> [<name> ...]

For every name, reads <out dir>/<name>.base.out and <name>.cut.out (lean's diagnostics and
`#print axioms` output). Messages are normalized by dropping the `file:line:col: ` prefix; the
two multisets must be equal and contain no error. Exit 1 otherwise.
"""
import re
import sys
from collections import Counter

PREFIX = re.compile(r"^\S+\.lean:\d+:\d+: ")


def msgs(path):
    out, cur = [], None
    for line in open(path, encoding="utf-8"):
        line = line.rstrip("\n")
        if PREFIX.match(line) or line.startswith("'"):
            if cur is not None:
                out.append(cur)
            cur = PREFIX.sub("", line)
        elif cur is not None:
            cur += "\n" + line
    if cur is not None:
        out.append(cur)
    return out


def main():
    d, names = sys.argv[1], sys.argv[2:]
    ok = True
    print("| importer | baseline messages | cut-check messages | errors | equal |")
    print("|---|---|---|---|---|")
    for n in names:
        b, c = msgs(f"{d}/{n}.base.out"), msgs(f"{d}/{n}.cut.out")
        errs = sum(1 for m in b + c if m.startswith("error"))
        eq = Counter(b) == Counter(c)
        ok = ok and eq and errs == 0
        print(f"| `{n}` | {len(b)} | {len(c)} | {errs} | {'yes' if eq else '**NO**'} |")
    print()
    print("CUT: PASS — every importer elaborates against the landed text with exactly its "
          "baseline diagnostics and axiom prints" if ok else "CUT: FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
