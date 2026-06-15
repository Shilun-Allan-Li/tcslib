"""
Validate blueprint <-> Lean correspondence and report remaining coverage.

Step 4 of the blueprint pipeline. Cross-checks every `\\lean{...}` and
`\\uses{...}` in the blueprint against dep_graph.json so the dataset built later
has trustworthy formal references.

Reports:
  * orphan \\lean        — label that names no declaration in dep_graph
  * dangling \\uses      — reference with no matching \\lean{...} anywhere
  * uncovered decls      — documentable declarations with no \\lean entry yet
  * per-area coverage    — covered / total documentable declarations

Usage:
    python3 scripts/blueprint_validate.py
    python3 scripts/blueprint_validate.py --strict   # exit 1 if orphans/dangling exist
"""

import argparse
import json
import re
from pathlib import Path

BASE = Path(__file__).resolve().parent.parent
DEP_GRAPH = BASE / "dep_graph.json"
CHAPTER_DIR = BASE / "blueprint" / "src" / "chapter"

# Mirror of blueprint_enumerate.py's policy.
_MODIFIERS = r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+|local\s+|nonrec\s+|@\[[^\]]*\]\s*)*"
DECL_RE = re.compile(r"^\s*" + _MODIFIERS + r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|example)\b")
KEEP_KINDS = {"theorem", "lemma", "def", "abbrev", "structure", "inductive", "class"}
LEAN_LABEL_RE = re.compile(r"\\lean\{([^}]*)\}")
USES_RE = re.compile(r"\\uses\{([^}]*)\}")


def load_modules() -> dict:
    with open(DEP_GRAPH) as f:
        return json.load(f)["modules"]


def module_to_lean_path(module: str) -> Path:
    rel = module[len("TCSlib."):] if module.startswith("TCSlib.") else module
    return BASE / "TCSlib" / (rel.replace(".", "/") + ".lean")


# Mirror of blueprint_enumerate.py: strip Lean's `_private.<module>.<n>.` mangling.
PRIVATE_RE = re.compile(r"^_private\..*?\.\d+\.")


def normalize_name(name: str) -> str:
    return PRIVATE_RE.sub("", name)


def documentable_decls(modules: dict) -> dict[str, str]:
    """name -> area, for every documentable declaration."""
    out: dict[str, str] = {}
    for module, mdata in modules.items():
        lean_path = module_to_lean_path(module)
        if not lean_path.exists():
            continue
        lines = lean_path.read_text(encoding="utf-8", errors="ignore").splitlines()
        area = module.split(".")[1] if module.count(".") >= 1 else module
        for name, dd in mdata["declarations"].items():
            lo = max(0, dd["startLine"] - 1)
            hi = min(len(lines), dd["endLine"])
            kind = None
            for i in range(lo, min(hi + 1, len(lines))):
                m = DECL_RE.match(lines[i])
                if m:
                    kind = m.group(1)
                    break
            if kind in KEEP_KINDS:
                out[normalize_name(name)] = area
    return out


def collect_labels():
    leans, uses = set(), set()
    for tex in CHAPTER_DIR.rglob("*.tex"):
        text = tex.read_text(encoding="utf-8", errors="ignore")
        for m in LEAN_LABEL_RE.finditer(text):
            for p in m.group(1).split(","):
                p = p.strip()
                if p:
                    leans.add(p)
        for m in USES_RE.finditer(text):
            for p in m.group(1).split(","):
                p = p.strip()
                if p:
                    uses.add(p)
    return leans, uses


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--strict", action="store_true")
    args = ap.parse_args()

    modules = load_modules()
    docs = documentable_decls(modules)
    all_decl_names = {normalize_name(n) for m in modules.values() for n in m["declarations"]}
    leans, uses = collect_labels()

    # \lean labels that look like Lean names (skip instance-arg blurbs like "[Field α]").
    lean_names = {l for l in leans if not l.startswith("[")}
    orphans = sorted(n for n in lean_names if n not in all_decl_names)
    dangling = sorted(u for u in uses if u not in leans and u not in all_decl_names)
    uncovered = sorted(n for n in docs if n not in leans)

    print("=== Blueprint validation ===")
    print(f"\\lean labels        : {len(leans)}")
    print(f"\\uses references     : {len(uses)}")
    print(f"Documentable decls   : {len(docs)}")
    print(f"Covered              : {len(docs) - sum(1 for n in docs if n not in leans)}")
    print()

    print(f"Orphan \\lean labels (not in dep_graph): {len(orphans)}")
    for n in orphans[:40]:
        print(f"  ? {n}")
    if len(orphans) > 40:
        print(f"  ... and {len(orphans) - 40} more")
    print()

    print(f"Dangling \\uses references (no \\lean target): {len(dangling)}")
    for n in dangling[:40]:
        print(f"  ! {n}")
    if len(dangling) > 40:
        print(f"  ... and {len(dangling) - 40} more")
    print()

    # Per-area coverage summary.
    by_area: dict[str, list[int]] = {}
    for name, area in docs.items():
        cell = by_area.setdefault(area, [0, 0])
        cell[1] += 1
        if name in leans:
            cell[0] += 1
    print("Coverage by area (covered / documentable):")
    for area in sorted(by_area):
        cov, tot = by_area[area]
        print(f"  {area:24s} {cov:4d} / {tot:4d}")
    print()
    print(f"Remaining uncovered documentable decls: {len(uncovered)}")

    if args.strict and (orphans or dangling):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
