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
  * \\uses cycles        — dependency cycles between blueprint entries. The
                           web build (plastexdepgraph) recurses through \\uses
                           without cycle detection, so any cycle crashes it with
                           RecursionError; cycles therefore always fail (exit 1).

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


ENTRY_LEAN_RE = re.compile(r"^\s*\\lean\{([^}]*)\}")
END_ENV_RE = re.compile(r"\\end\{\w+\}")


def collect_entry_uses(chapter_dir: Path = CHAPTER_DIR) -> dict[str, set[str]]:
    """label -> the labels named in that entry's \\uses (statement and proof alike)."""
    edges: dict[str, set[str]] = {}
    for tex in chapter_dir.rglob("*.tex"):
        current: list[str] = []
        for block in END_ENV_RE.split(tex.read_text(encoding="utf-8", errors="ignore")):
            labels = []
            for line in block.splitlines():
                m = ENTRY_LEAN_RE.match(line)
                if m:
                    labels = [p.strip() for p in m.group(1).split(",") if p.strip()]
            used = {p.strip() for m in USES_RE.finditer(block)
                    for p in m.group(1).split(",") if p.strip()}
            # A proof environment has no \\lean of its own; it belongs to the
            # statement just before it.
            owners = labels or current
            for owner in owners:
                edges.setdefault(owner, set()).update(used - {owner})
            current = labels or current
    return edges


def find_cycles(edges: dict[str, set[str]]) -> list[list[str]]:
    """Strongly connected components of size > 1 (or self-loops), found iteratively."""
    index: dict[str, int] = {}
    low: dict[str, int] = {}
    on_stack: set[str] = set()
    stack: list[str] = []
    cycles: list[list[str]] = []
    counter = 0
    for root in edges:
        if root in index:
            continue
        work = [(root, iter(sorted(edges.get(root, ()))))]
        index[root] = low[root] = counter
        counter += 1
        stack.append(root)
        on_stack.add(root)
        while work:
            node, it = work[-1]
            advanced = False
            for nxt in it:
                if nxt not in edges:
                    continue
                if nxt not in index:
                    index[nxt] = low[nxt] = counter
                    counter += 1
                    stack.append(nxt)
                    on_stack.add(nxt)
                    work.append((nxt, iter(sorted(edges.get(nxt, ())))))
                    advanced = True
                    break
                if nxt in on_stack:
                    low[node] = min(low[node], index[nxt])
            if advanced:
                continue
            work.pop()
            if work:
                parent = work[-1][0]
                low[parent] = min(low[parent], low[node])
            if low[node] == index[node]:
                comp = []
                while True:
                    w = stack.pop()
                    on_stack.discard(w)
                    comp.append(w)
                    if w == node:
                        break
                if len(comp) > 1 or node in edges.get(node, ()):
                    cycles.append(sorted(comp))
    return cycles


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

    cycles = find_cycles(collect_entry_uses())
    print()
    print(f"\\uses cycles (crash the plasTeX web build): {len(cycles)}")
    for comp in cycles[:20]:
        print("  ↻ " + " -> ".join(comp))
    if len(cycles) > 20:
        print(f"  ... and {len(cycles) - 20} more")

    if cycles:
        return 1
    if args.strict and (orphans or dangling):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
