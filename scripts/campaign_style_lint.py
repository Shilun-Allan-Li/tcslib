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
# `--check8b` (opt-in; user, 2026-10-17: after the #118 briefs issue) adds check 8b below.
CHECK8B = "--check8b" in sys.argv[1:]
_ARGS = [a for a in sys.argv[1:] if a != "--check8b"]
SUBTREE = Path(_ARGS[0]) if _ARGS else Path("TCSlib/Complexity")

SIZE_TARGET = 600     # policy section 1: target upper end
SIZE_THRESHOLD = 1000 # policy section 1: split unless positively justified

# Vendored files follow upstream style (policy section 2, Statement prose:
# exempt from the docstring-presence requirement, and frozen anyway).
VENDORED = {
    "TCSlib/Complexity/TuringMachine/Configuration.lean",
    "TCSlib/Complexity/TuringMachine/Deterministic.lean",
    # vendored from [AFM26] anthropics/formal-math 3sum-apsp (design §15b)
    "TCSlib/Programs/Light/Assigns.lean",
    "TCSlib/Programs/Light/Calls.lean",
    "TCSlib/Programs/Light/Compiler/CallFrames.lean",
    "TCSlib/Programs/Light/Compiler/Cells.lean",
    "TCSlib/Programs/Light/Compiler/Conditions.lean",
    "TCSlib/Programs/Light/Compiler/Dispatcher.lean",
    "TCSlib/Programs/Light/Compiler/Expressions.lean",
    "TCSlib/Programs/Light/Compiler/ProgramCode.lean",
    "TCSlib/Programs/Light/Compiler/Simulation.lean",
    "TCSlib/Programs/Light/Compiler/StartUp.lean",
    "TCSlib/Programs/Light/Compiler/StatementCode.lean",
    "TCSlib/Programs/Light/Compiler/WholeProgram.lean",
    "TCSlib/Programs/Light/Frames.lean",
    "TCSlib/Programs/Light/Lib/ArrayAt.lean",
    "TCSlib/Programs/Light/Lib/Copy.lean",
    "TCSlib/Programs/Light/Lib/CountSort.lean",
    "TCSlib/Programs/Light/Lib/Emod.lean",
    "TCSlib/Programs/Light/Lib/Logs.lean",
    "TCSlib/Programs/Light/Lib/Merge.lean",
    "TCSlib/Programs/Light/Lib/MergeSort.lean",
    "TCSlib/Programs/Light/Lib/NextPair.lean",
    "TCSlib/Programs/Light/Lib/Odometer.lean",
    "TCSlib/Programs/Light/Lib/Pass.lean",
    "TCSlib/Programs/Light/Lib/PowTable.lean",
    "TCSlib/Programs/Light/Lib/RadixPass.lean",
    "TCSlib/Programs/Light/Lib/Seg.lean",
    "TCSlib/Programs/Light/Lib/Sqrt.lean",
    "TCSlib/Programs/Light/Logic.lean",
    "TCSlib/Programs/Light/Regions.lean",
    "TCSlib/Programs/Light/Rules.lean",
    "TCSlib/Programs/Light/RunsStayInLimits.lean",
    "TCSlib/Programs/Light/Syntax.lean",
    "TCSlib/Programs/Light/Tactics.lean",
    "TCSlib/Programs/Util/Basic.lean",
    "TCSlib/Programs/Util/CountingSort.lean",
    "TCSlib/Programs/Util/Index.lean",
    "TCSlib/Programs/Util/List.lean",
    "TCSlib/Programs/Util/Odometer.lean",
    "TCSlib/Programs/Util/StablePass.lean",
    "TCSlib/Programs/WordRAM/Basic.lean",
    "TCSlib/Programs/WordRAM/Steps.lean",
}

# Declaration kinds requiring statement prose (instances exempt per policy).
DOC_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?(private\s+)?(?:noncomputable\s+)?"
    r"(theorem|lemma|def|structure|abbrev|inductive)\s+([A-Za-z0-9_.']+)"
)
ATTR_LINE_RE = re.compile(r"^@\[[^\]]*\]$")
SET_OPTIONS = [
    "set_option maxHeartbeats 0",
    "set_option relaxedAutoImplicit false",
    "set_option autoImplicit false",
]
DOCSTRING_RE = re.compile(r"/--.*?-/", re.S)
DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(private\s+)?(?:noncomputable\s+)?"
    r"(theorem|def|lemma|structure|abbrev|instance|inductive)\s+([A-Za-z0-9_.']+)",
    re.M,
)

# Check 8 (policy section 1, definitions land with their lemmas; user, 2026-10-16).
API_DEF_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:noncomputable|protected)\s+)*(private\s+)?"
    r"(?:(?:noncomputable|protected)\s+)*def\s+([A-Za-z0-9_.']+)",
    re.M,
)
API_LEMMA_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:protected\s+)?(private\s+)?(?:protected\s+)?"
    r"(?:theorem|lemma)\s+([A-Za-z0-9_.']+)",
    re.M,
)
API_ATTR_RE = re.compile(
    r"^attribute\s*\[([^\]]*)\]((?:[ \t]*[A-Za-z0-9_.'«»]+|[ \t]*\n[ \t]+[A-Za-z0-9_.'«»]+)+)",
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


# Check 8b (opt-in, `--check8b`): structure-valued definitions need their fields as equations.
FIELDS8B = {
    "Cfg": ["state", "inputPos", "workTapes", "workTapePos", "output"],
    "Action": ["inputTape", "workTapes", "output", "state"],
    "FinTM": ["k", "State", "tm"],
    "FinNDTM": ["k", "State", "tm"],
    "Contract": ["pre", "time", "post", "lo", "hi"],
    "RoundContract": ["pre", "time", "post", "lo", "hi"],
    "ReturnContract": ["pre", "time", "post", "lo", "hi"],
}


def uncovered_fields(stripped: str) -> list:
    """Public `def`s whose value is a configuration, an action, a bundled machine or a contract
    (`FIELDS8B`), with neither a `simps` attribute, nor an unfolding `<def>_eq`, nor a
    `<def>_<field>` lemma for every data field (check 8b; policy section 1). Machine-valued
    definitions are left to check 8, which accepts their run lemmas; so are definitions whose body
    is not a structure literal (recursion, an application), and bundled machines with a `_computes`
    or `_run` lemma. A heuristic on the result type's head: it reports names, review judges them."""
    def last(n):
        return n.rsplit(".", 1)[-1]

    lemmas = {last(m.group(2)) for m in API_LEMMA_RE.finditer(stripped) if not m.group(1)}
    simps = set()
    for m in API_ATTR_RE.finditer(stripped):
        if "simps" in m.group(1):
            simps.update(last(x) for x in m.group(2).split())
    out = []
    for m in API_DEF_RE.finditer(stripped):
        if m.group(1):
            continue
        name = last(m.group(2))
        rest = stripped[m.end():]
        cut = min([i for i in (rest.find(":="), rest.find(" where"), rest.find("\n  |")) if i >= 0] or [len(rest)])
        header = rest[:cut]
        depth, colon = 0, -1
        for i, ch in enumerate(header):
            if ch in "([{⟨": depth += 1
            elif ch in ")]}⟩": depth -= 1
            elif ch == ":" and depth == 0: colon = i
        if colon < 0:
            continue
        rtype = header[colon + 1:].split("→")[-1].strip()
        head = rtype.split()[0].strip("(") if rtype.split() else ""
        head = last(head)
        if head not in FIELDS8B:
            continue
        body = rest[cut:].lstrip()
        if body.startswith(":="):
            body = body[2:].lstrip()
        literal = body.startswith(("where", "⟨", "{"))
        if not literal:
            continue  # recursion or an application: check 8 asks for its equation
        if head in ("FinTM", "FinNDTM") and any(
                l.startswith(name + "_") and ("comput" in l or "run" in l) for l in lemmas):
            continue  # a bundled machine read through its run or computation lemma
        line_start = stripped.rfind("\n", 0, m.start()) + 1
        attrs = stripped[line_start:m.start() + 40]
        if "simps" in attrs or name in simps or name + "_eq" in lemmas:
            continue
        if all(f"{name}_{f}" in lemmas for f in FIELDS8B[head]):
            continue
        out.append(name)
    return out


def uncovered_defs(stripped: str) -> list:
    """Public `def`s with no published lemma beside them (check 8). A definition is covered when
    a `simps` attribute is attached to it, or when a public theorem or lemma of the same file is
    named after it: the last name component begins with the definition's last component and an
    underscore (`zoneSlot_of_lt`, `recordAt_iff` for `RecordAt`), or, for a machine `fooTM`, with
    `foo_` (its run or contract lemma, `prefixCanon_run`). Abbreviations, structures, inductives
    and instances are exempt. A heuristic: it reports names, review judges them."""
    def last(n):
        return n.rsplit(".", 1)[-1]

    def low1(n):
        return n[:1].lower() + n[1:]

    lemmas = [last(m.group(2)) for m in API_LEMMA_RE.finditer(stripped) if not m.group(1)]
    simps = set()
    for m in API_ATTR_RE.finditer(stripped):
        if "simps" in m.group(1):
            simps.update(last(t) for t in m.group(2).split())
    lines = stripped.splitlines()
    starts = [0]
    for ln in lines:
        starts.append(starts[-1] + len(ln) + 1)
    out = []
    for m in API_DEF_RE.finditer(stripped):
        if m.group(1):
            continue
        name = last(m.group(2))
        # attributes on the definition: its own line, and the attribute lines just above it
        li = max(i for i, st in enumerate(starts) if st <= m.start())
        attrs = lines[li]
        j = li - 1
        while j >= 0 and lines[j].strip().startswith("@["):
            attrs += lines[j]
            j -= 1
        if "simps" in attrs or name in simps:
            continue
        prefixes = {name + "_", low1(name) + "_"}
        if name.endswith("TM") and len(name) > 2:
            prefixes |= {name[:-2] + "_", low1(name[:-2]) + "_"}
        if any(l.startswith(p) for l in lemmas for p in prefixes):
            continue
        out.append(m.group(2))
    return out


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

    # 8. Definitions land with their lemmas (policy section 1; user, 2026-10-16): every public
    #    `def` has an equation, field or run lemma beside it. WARN, with the names, so that a
    #    head-against-base diff shows any new definition that lacks one. Vendored files exempt.
    if str(rel) not in VENDORED:
        bare = uncovered_defs(stripped)
        if bare:
            note("WARN", rel, f"{len(bare)} public def(s) without a lemma beside them "
                              f"(check 8): {', '.join(sorted(bare))}")
        if CHECK8B:
            nofields = uncovered_fields(stripped)
            if nofields:
                note("WARN", rel, f"{len(nofields)} structure-valued def(s) without field equations "
                                  f"(check 8b): {', '.join(sorted(nofields))}")

    # 7. Statement prose (policy section 2): every public declaration
    #    (instances and vendored files exempt) is immediately preceded by a
    #    docstring, skipping attribute / `open ... in` / `noncomputable` lines.
    #    Presence only; statement *quality* is review judgment.
    if str(rel) not in VENDORED:
        depth = 0
        for idx, line in enumerate(lines):
            if depth == 0:
                m = DOC_DECL_RE.match(line)
                if m and not m.group(1):
                    j = idx - 1
                    while j >= 0:
                        prev = lines[j].strip()
                        if (ATTR_LINE_RE.fullmatch(prev)
                                or (prev.startswith("open ") and prev.endswith(" in"))
                                or prev == "noncomputable"):
                            j -= 1
                            continue
                        break
                    if not (j >= 0 and lines[j].rstrip().endswith("-/")):
                        note("FAIL", rel,
                             f"line {idx + 1}: public {m.group(2)} "
                             f"`{m.group(3)}` has no preceding docstring "
                             "(policy section 2, statement prose)")
            depth += line.count("/-") - line.count("-/")


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
