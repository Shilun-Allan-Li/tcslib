"""Compare static sorry counts with replay counts; fail closed on a discrepancy.

Usage: python3 -I staticsorry.py <source root> <replay log> [module plan]
Supply the ordered module plan for replay gates to detect missing, duplicate,
out-of-order, and unexpected count rows.
"""
from pathlib import Path
import argparse
import re

def strip(src):
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i): depth += 1; i += 2; continue
        if src.startswith("-/", i) and depth > 0: depth -= 1; i += 2; continue
        if depth == 0: out.append(src[i])
        i += 1
    return "\n".join(l.split("--")[0] for l in "".join(out).splitlines())
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(theorem|lemma|def|abbrev|instance|example|structure|inductive)\b", re.M)

ROW = re.compile(r"(\S+) exit=\d+ errors=\d+ sorry=(\d+)")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path)
    parser.add_argument("log", type=Path)
    parser.add_argument("module_plan", type=Path, nargs="?")
    args = parser.parse_args()
    rows = []
    for line in args.log.read_text(encoding="utf-8").splitlines():
        if match := ROW.fullmatch(line.strip()):
            rows.append((match[1], int(match[2])))
    modules = [name for name, _ in rows]
    invalid = False
    if not modules:
        print("COVERAGE no replay count rows")
        invalid = True
    if len(modules) != len(set(modules)):
        print("COVERAGE duplicate replay count rows")
        invalid = True
    if args.module_plan is not None:
        expected = [line.strip() for line in
                    args.module_plan.read_text(encoding="utf-8").splitlines() if line.strip()]
        if not expected or len(expected) != len(set(expected)):
            print("COVERAGE module plan is empty or contains duplicate modules")
            invalid = True
        if modules != expected:
            missing = sorted(set(expected) - set(modules))
            extra = sorted(set(modules) - set(expected))
            print(f"COVERAGE expected {len(expected)} ordered rows, got {len(modules)}")
            if missing:
                print("MISSING", *missing)
            if extra:
                print("UNEXPECTED", *extra)
            invalid = True
    bad = total = 0
    for name, observed in rows:
        rel = Path(name)
        if rel.is_absolute() or ".." in rel.parts:
            print("COVERAGE invalid module path", name)
            invalid = True
            continue
        try:
            source = strip((args.root / (name + ".lean")).read_text(encoding="utf-8"))
        except (OSError, UnicodeError) as e:
            print("COVERAGE unreadable source for", name, e)
            invalid = True
            continue
        starts = [match.start() for match in DECL.finditer(source)] + [len(source)]
        actual = sum(1 for a, b in zip(starts, starts[1:]) if re.search(r"\bsorry\b", source[a:b]))
        total += actual
        if actual != observed:
            bad += 1
            print("MISMATCH", name, "static", actual, "replay", observed)
    print(f"modules {len(rows)}, mismatches {bad}, static total {total}")
    return int(invalid or bad != 0)


if __name__ == "__main__":
    raise SystemExit(main())
