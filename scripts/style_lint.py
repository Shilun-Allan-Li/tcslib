#!/usr/bin/env python3
"""
Mechanical checks for policy.md (Review checklist items 1–5, presence only).

    python3 scripts/style_lint.py <file.lean>... | --area <Area>

Per file: copyright block; the three set_options; no bare `import Mathlib`; module
docstring headings (# Title, ## Main definitions, ## Main results, ## References);
placeholder References; facade has ## Contents; every public non-instance declaration
has a `/-- … -/` docstring; proofs > 20 lines have **Proof sketch.**; size > 1000.
Statement *quality* is review judgment, not checked here.  Exit 1 if any finding.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(private |protected |noncomputable |nonrec )*"
                  r"(theorem|lemma|def|instance|structure|inductive|abbrev|class|opaque|axiom)\b")
OPTS = ["set_option maxHeartbeats 0", "set_option relaxedAutoImplicit false",
        "set_option autoImplicit false"]
HEADINGS = ["## Main definitions", "## Main results", "## References"]


def lint(path: Path) -> list[str]:
    out: list[str] = []
    text = path.read_text()
    lines = text.split("\n")
    rel = path.resolve().relative_to(ROOT)
    is_facade = (path.with_suffix("")).is_dir()

    if "Copyright" not in text[:1500]:
        out.append(f"{rel}: missing copyright block")
    for o in OPTS:
        if o not in text:
            out.append(f"{rel}: missing `{o}`")
    if re.search(r"^import Mathlib\s*$", text, re.M):
        out.append(f"{rel}: bare `import Mathlib`")
    m = re.search(r"/-!(.*?)-/", text, re.S)
    doc = m.group(1) if m else ""
    if not re.search(r"^# ", doc, re.M):
        out.append(f"{rel}: module docstring has no `# Title`")
    if is_facade:
        if "## Contents" not in doc:
            out.append(f"{rel}: facade without `## Contents`")
    else:
        for h in HEADINGS:
            if h not in doc:
                out.append(f"{rel}: module docstring missing `{h}`")
        refs = doc.split("## References", 1)[1] if "## References" in doc else ""
        if refs and not re.search(r"\[[A-Za-z]+\d{2}[a-z]?\]|\*[^*]+\*", refs):
            out.append(f"{rel}: `## References` has no citation (placeholder?)")
    if len(lines) > 1000:
        out.append(f"{rel}: {len(lines)} lines (> 1000, must split)")

    starts = [i for i, l in enumerate(lines) if DECL.match(l)]
    starts.append(len(lines))
    for k, i in enumerate(starts[:-1]):
        mm = DECL.match(lines[i])
        kind = mm.group(2)
        private = "private " in (mm.group(0))
        name = re.sub(r"^.*?\b" + kind + r"\s+", "", lines[i]).split()[0] if lines[i].split() else "?"
        up = i - 1
        while up >= 0 and (lines[up].strip() == "" or lines[up].lstrip().startswith("@[")):
            up -= 1
        has_doc = up >= 0 and lines[up].rstrip().endswith("-/") and "/-!" not in lines[up]
        if kind != "instance" and not private and not has_doc:
            out.append(f"{rel}:{i+1}: public `{kind} {name}` has no docstring")
        if kind in ("theorem", "lemma"):
            # proof region ends at the next declaration OR at the next docstring/module
            # comment/attribute that introduces it (otherwise the next docstring is counted)
            end = starts[k + 1]
            for j in range(i + 1, starts[k + 1]):
                if re.match(r"^\s*(/--|/-!|@\[)", lines[j]):
                    end = j
                    break
            body = [l for l in lines[i:end] if l.strip() and not l.strip().startswith("--")]
            if len(body) > 20:
                # find the docstring block above
                j = up
                while j >= 0 and not lines[j].lstrip().startswith("/--"):
                    j -= 1
                ds = "\n".join(lines[max(j, 0):i]) if has_doc else ""
                if "Proof sketch" not in ds:
                    out.append(f"{rel}:{i+1}: `{name}` proof is {len(body)} lines, no **Proof sketch.**")
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--area", action="append", default=[])
    ap.add_argument("--summary", action="store_true")
    ap.add_argument("files", nargs="*")
    a = ap.parse_args()
    files = [Path(f) for f in a.files]
    for ar in a.area:
        files += sorted((ROOT / "TCSlib" / ar).rglob("*.lean"))
    total = 0
    for f in files:
        fs = lint(f)
        total += len(fs)
        if a.summary:
            print(f"{len(fs):4d}  {f.resolve().relative_to(ROOT)}")
        else:
            print("\n".join(fs))
    print(f"\n{total} findings in {len(files)} files", file=sys.stderr)
    return 1 if total else 0


if __name__ == "__main__":
    sys.exit(main())
