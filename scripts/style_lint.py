#!/usr/bin/env python3
"""Mechanical policy.md conformance lint for the Arora-Barak Chapter 1 tree.

Checks the mechanically checkable slice of policy.md (sections 1-3) plus the
campaign's standing conventions, so external audit rounds can consume a
reported attestation instead of performing style review (epoch-1/epoch-2
practice; see AroraBarakChapter1Plan.md section 5).

  FAIL  - unambiguous policy violation; exit code 1.
  WARN  - needs a recorded justification (e.g. a file over the 1000-line
          threshold with an escalation on file); exit code 0.
  INFO  - context only.

Usage: python3 scripts/style_lint.py [subtree]   (default: TCSlib/Complexity)
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SUBTREE = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("TCSlib/Complexity")

SIZE_TARGET = 600     # policy section 1: target upper end
SIZE_THRESHOLD = 1000 # policy section 1: split unless positively justified
SET_OPTIONS = [
    "set_option maxHeartbeats 0",
    "set_option relaxedAutoImplicit false",
    "set_option autoImplicit false",
]
DOCSTRING_RE = re.compile(r"/--.*?-/", re.S)
DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(private\s+)?"
    r"(theorem|def|lemma|structure|abbrev|instance|inductive)\s+([A-Za-z0-9_.']+)",
    re.M,
)

findings = []  # (level, path, message)


def note(level, path, msg):
    findings.append((level, str(path), msg))


def strip_comments(src: str) -> str:
    """Remove nesting-aware block comments (docstrings included) and line
    comments, so declaration counting never matches prose like `lemma advances`
    inside a docstring (epoch-2 audit, finding 3)."""
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


def is_facade(path: Path) -> bool:
    return (path.parent / path.stem).is_dir()


def check_file(path: Path):
    src = path.read_text()
    lines = src.splitlines()
    rel = path.relative_to(ROOT)

    # 1. Size (policy section 1).
    n = len(lines)
    if n > SIZE_THRESHOLD:
        note("WARN", rel, f"{n} lines > {SIZE_THRESHOLD}: policy requires a split "
                          "or a recorded justification (escalation/decision log)")
    elif n > SIZE_TARGET and not is_facade(path):
        note("INFO", rel, f"{n} lines > target {SIZE_TARGET}")

    # 2. Imports (policy section 1).
    if re.search(r"^import Mathlib$", src, re.M):
        note("FAIL", rel, "bare `import Mathlib`")

    # 3. References section (policy section 2) - math files and facades alike.
    if "## References" not in src and not is_facade(path):
        note("FAIL", rel, "module docstring lacks a `## References` section")

    # 4. Standard set_option header (campaign convention; facades exempt).
    if not is_facade(path):
        missing = [o for o in SET_OPTIONS if o not in src]
        if missing:
            note("WARN", rel, f"missing header option(s): {', '.join(missing)}")

    # 5. Every sorry is preceded by a docstring mentioning a proof sketch
    #    (policy section 3). Heuristic: nearest docstring above the sorry line.
    for i, line in enumerate(lines):
        if line.strip() == "sorry":
            head = "\n".join(lines[:i])
            docs = DOCSTRING_RE.findall(head)
            if not docs or "sketch" not in docs[-1].lower():
                note("FAIL", rel, f"line {i + 1}: `sorry` without a proof sketch "
                                  "in the preceding docstring")

    # 6. Public/private declaration tally (INFO - context for audit packs).
    #    Counted on comment-stripped source (epoch-2 audit, finding 3).
    stripped = strip_comments(src)
    pub = sum(1 for m in DECL_RE.finditer(stripped) if not m.group(1))
    priv = sum(1 for m in DECL_RE.finditer(stripped) if m.group(1))
    note("INFO", rel, f"{n} lines; {pub} public / {priv} private declarations")


def check_facade(path: Path):
    """Every child .lean under the facade's directory must be imported."""
    src = path.read_text()
    rel = path.relative_to(ROOT)
    child_dir = path.parent / path.stem
    for child in sorted(child_dir.rglob("*.lean")):
        mod = ".".join(child.relative_to(ROOT).with_suffix("").parts)
        if not is_facade(child) and f"import {mod}" not in src:
            # A grandchild may legitimately be imported via its own facade.
            inter = child.parent / (child.parent.name + ".lean")
            covered = inter != path and inter.exists() and \
                f"import {'.'.join(inter.relative_to(ROOT).with_suffix('').parts)}" in src
            if not covered:
                note("FAIL", rel, f"facade does not import child module `{mod}`")


def main():
    files = sorted((ROOT / SUBTREE).rglob("*.lean"))
    if not files:
        print(f"no .lean files under {SUBTREE}", file=sys.stderr)
        return 2
    for f in files:
        check_file(f)
        if is_facade(f):
            check_facade(f)

    width = max(len(p) for _, p, _ in findings)
    failed = False
    for level in ("FAIL", "WARN", "INFO"):
        for lv, p, msg in findings:
            if lv == level:
                print(f"{lv:4}  {p:<{width}}  {msg}")
                failed |= lv == "FAIL"
    print(f"\nstyle_lint: {sum(1 for l, _, _ in findings if l == 'FAIL')} FAIL, "
          f"{sum(1 for l, _, _ in findings if l == 'WARN')} WARN over {len(files)} files")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
