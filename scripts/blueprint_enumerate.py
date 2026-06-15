"""
Plan the blueprint-extraction sweep deterministically from dep_graph.json.

This is step 1 of the blueprint pipeline (see blueprint/BLUEPRINT_PIPELINE.md).
It does NOT write any prose — it only decides *what work exists* so that the
orchestrator can fan out one `blueprint-writer` subagent per module.

For every TCSlib module it produces a "work unit" JSON listing the declarations
that (a) are of a documentable kind (theorem / lemma / def / abbrev / structure /
inductive / class — instances and examples are skipped) and (b) do not already
have a `\\lean{...}` entry anywhere in the blueprint. Each declaration entry is
pre-loaded with its docstring, statement signature, exact line range, and the
intra-project dependencies that should become its `\\uses{...}` list — so the
subagent only has to write the informal mathematical description.

Outputs (under blueprint/.work/):
    manifest.json            ← overview + list of per-module work files
    <Module_With_Underscores>.json  ← one work unit per module that has work

Usage:
    python3 scripts/blueprint_enumerate.py                # plan everything
    python3 scripts/blueprint_enumerate.py --module BooleanAnalysis.LMN.GateMerge
    python3 scripts/blueprint_enumerate.py --include-covered   # re-emit even covered decls
"""

import argparse
import json
import re
from pathlib import Path

BASE = Path(__file__).resolve().parent.parent  # tcstcslib/
DEP_GRAPH = BASE / "dep_graph.json"
CHAPTER_DIR = BASE / "blueprint" / "src" / "chapter"
WORK_DIR = BASE / "blueprint" / ".work"

# Declaration kinds that get a blueprint entry, mapped to the LaTeX environment.
KIND_ENV = {
    "theorem": "theorem",
    "lemma": "lemma",
    "def": "definition",
    "abbrev": "definition",
    "structure": "definition",
    "inductive": "definition",
    "class": "definition",
}
# Kinds we deliberately skip (plumbing / not a math statement).
SKIP_KINDS = {"instance", "example"}

# Matches the declaration keyword, tolerating modifiers and attributes.
_MODIFIERS = r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+|local\s+|nonrec\s+|@\[[^\]]*\]\s*)*"
DECL_RE = re.compile(
    r"^\s*" + _MODIFIERS + r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|example)\b"
)
LEAN_LABEL_RE = re.compile(r"\\lean\{([^}]*)\}")


def load_modules() -> dict:
    with open(DEP_GRAPH) as f:
        return json.load(f)["modules"]


def module_to_lean_path(module: str) -> Path:
    rel = module[len("TCSlib."):] if module.startswith("TCSlib.") else module
    return BASE / "TCSlib" / (rel.replace(".", "/") + ".lean")


def module_to_tex_path(module: str) -> Path:
    rel = module[len("TCSlib."):] if module.startswith("TCSlib.") else module
    return CHAPTER_DIR / (rel.replace(".", "/") + ".tex")


def camel_split(name: str) -> str:
    """`GateMerge` -> `Gate Merge`, `LDC` stays `LDC`, `TwoXOR` -> `Two XOR`."""
    s = re.sub(r"(?<=[a-z0-9])(?=[A-Z])", " ", name)
    s = re.sub(r"(?<=[A-Z])(?=[A-Z][a-z])", " ", s)
    return s.replace("_", " ").strip()


def covered_lean_labels() -> set[str]:
    """Every `\\lean{name}` already present anywhere in the blueprint chapters."""
    covered: set[str] = set()
    if not CHAPTER_DIR.exists():
        return covered
    for tex in CHAPTER_DIR.rglob("*.tex"):
        text = tex.read_text(encoding="utf-8", errors="ignore")
        for m in LEAN_LABEL_RE.finditer(text):
            for part in m.group(1).split(","):
                part = part.strip()
                if part:
                    covered.add(part)
    return covered


def extract_docstring(lines: list[str], decl_idx: int, max_lines: int = 40):
    """Return the `/-- ... -/` doc comment directly above the declaration, else None.

    Only a *true* Lean doc comment counts: a `/-- ... -/` block whose closing `-/` sits
    immediately above the declaration keyword (modulo `@[...]` attribute lines). Plain
    `/- ... -/` block comments and `/-! ... -/` section comments are NOT docstrings and
    must never be captured — and the search for the opener stops at the first comment
    boundary so it can never run up into a neighbouring declaration's body.
    """
    j = decl_idx - 1
    # Doc comments may be separated from the decl only by attribute lines.
    while j >= 0 and lines[j].strip().startswith("@["):
        j -= 1
    if j < 0 or not lines[j].rstrip().endswith("-/"):
        return None
    stripped = lines[j].lstrip()
    # Single-line docstring: `/-- ... -/` all on one line.
    if stripped.startswith("/--"):
        return stripped.replace("/--", "").replace("-/", "").strip()
    # Reject a single-line non-doc comment `/- ... -/` (e.g. a section label).
    if stripped.startswith("/-"):
        return None
    # Multi-line: walk up to the opener, which must be `/--`. Bail at any other comment
    # boundary so we never absorb earlier declarations.
    k = j
    while k >= 0 and (j - k) <= max_lines:
        s = lines[k].lstrip()
        if s.startswith("/--"):
            return "\n".join(lines[k:j + 1]).replace("/--", "").replace("-/", "").strip()
        if s.startswith("/-"):
            return None  # opener of a non-doc comment ( /- or /-! )
        if k != j and lines[k].rstrip().endswith("-/"):
            return None  # closing of a different, earlier comment
        k -= 1
    return None


def detect_kind_and_doc(lines: list[str], start: int, end: int):
    """Return (kind, decl_line_index, doc_or_None) scanning the declaration window.

    `lines` is 0-indexed; `start`/`end` are 1-indexed inclusive (dep_graph convention).
    """
    lo = max(0, start - 1)
    hi = min(len(lines), end)
    kind = None
    decl_idx = None
    # Find the first real declaration keyword in the window.
    for i in range(lo, min(hi + 1, len(lines))):
        m = DECL_RE.match(lines[i])
        if m:
            kind = m.group(1)
            decl_idx = i
            break
    if decl_idx is None:
        return None, None, None
    return kind, decl_idx, extract_docstring(lines, decl_idx)


def extract_signature(lines: list[str], decl_idx: int, end: int, cap: int = 25) -> str:
    """Statement head: from the keyword line up to (and including) the proof/body `:=`."""
    out = []
    hi = min(len(lines), max(end, decl_idx + 1))
    for i in range(decl_idx, min(decl_idx + cap, hi)):
        line = lines[i]
        if ":=" in line:
            out.append(line[: line.index(":=") + 2])
            break
        out.append(line)
        if i == decl_idx + cap - 1:
            out.append("    ...")
    return "\n".join(s.rstrip() for s in out).strip()


# Lean mangles `private` declarations as `_private.<module>.<n>.<RealQualifiedName>`.
# The blueprint must reference the clean qualified name (what source code and the
# existing chapters use), so strip the mangling for every \lean/\uses label.
PRIVATE_RE = re.compile(r"^_private\..*?\.\d+\.")


def normalize_name(name: str) -> str:
    return PRIVATE_RE.sub("", name)


def build_kept_global(modules: dict) -> set[str]:
    """All declaration names (across TCSlib) whose kind is documentable.

    Used to filter `\\uses{...}` so it only references nodes that will get a label.
    Kind is re-derived from source so it matches the entry decision exactly.
    """
    kept: set[str] = set()
    for module, mdata in modules.items():
        lean_path = module_to_lean_path(module)
        if not lean_path.exists():
            continue
        lines = lean_path.read_text(encoding="utf-8", errors="ignore").splitlines()
        for name, dd in mdata["declarations"].items():
            kind, _, _ = detect_kind_and_doc(lines, dd["startLine"], dd["endLine"])
            if kind in KIND_ENV:
                kept.add(normalize_name(name))
    return kept


def build_work_unit(module: str, mdata: dict, kept_global: set[str],
                    covered: set[str], include_covered: bool, claimed: set[str]):
    lean_path = module_to_lean_path(module)
    if not lean_path.exists():
        return None
    lines = lean_path.read_text(encoding="utf-8", errors="ignore").splitlines()
    tex_path = module_to_tex_path(module)
    rel_lean = lean_path.relative_to(BASE).as_posix()
    rel_tex = tex_path.relative_to(BASE).as_posix()
    area = module.split(".")[1] if module.count(".") >= 1 else module

    decls = []
    # Stable order: by source line.
    for name, dd in sorted(mdata["declarations"].items(), key=lambda kv: kv[1]["startLine"]):
        nname = normalize_name(name)
        if nname in covered and not include_covered:
            continue
        # Two `private` decls in different modules can share a name once the
        # `_private.<module>.<n>.` mangling is stripped. A blueprint label must be
        # unique, so the first module (sorted order) claims the name; later ones skip
        # it to avoid a duplicate \lean{...} binding.
        if nname in claimed:
            continue
        kind, decl_idx, doc = detect_kind_and_doc(lines, dd["startLine"], dd["endLine"])
        if kind not in KIND_ENV:
            continue
        claimed.add(nname)
        uses = sorted({
            nd for d in dd.get("deps", [])
            if d.get("module", "").startswith("TCSlib")
            for nd in [normalize_name(d["name"])]
            if nd in kept_global and nd != nname
        })
        decls.append({
            "name": nname,
            "kind": kind,
            "env": KIND_ENV[kind],
            "startLine": dd["startLine"],
            "endLine": dd["endLine"],
            "uses": uses,
            "doc": doc,
            "signature": extract_signature(lines, decl_idx, dd["endLine"]),
        })

    if not decls:
        return None
    return {
        "module": module,
        "area": area,
        "lean_file": rel_lean,
        "target_tex": rel_tex,
        "target_exists": tex_path.exists(),
        "chapter_title": camel_split(module.split(".")[-1]),
        "decls": decls,
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--module", help="Plan a single module (short or full name).")
    ap.add_argument("--include-covered", action="store_true",
                    help="Emit entries even for decls already in the blueprint.")
    args = ap.parse_args()

    if not DEP_GRAPH.exists():
        print(f"ERROR: {DEP_GRAPH} not found. Run scripts/build_dep_graph.py first.")
        return 1

    modules = load_modules()
    if args.module:
        wanted = args.module if args.module.startswith("TCSlib.") else f"TCSlib.{args.module}"
        modules = {m: d for m, d in modules.items() if m == wanted or m.endswith("." + args.module)}
        if not modules:
            print(f"No module matching {args.module!r}.")
            return 1

    covered = set() if args.include_covered else covered_lean_labels()
    print(f"Existing \\lean labels in blueprint: {len(covered)}")
    print("Re-deriving declaration kinds from source ...")
    full_graph = load_modules()
    kept_global = build_kept_global(full_graph)
    print(f"Documentable declarations across TCSlib: {len(kept_global)}")

    # dep_graph.json is the source of truth: a module is in it iff it compiled.
    # `.lean` files on disk that are absent from the graph did NOT compile and are
    # intentionally excluded (we only document real, \leanok-able statements).
    disk_modules = {
        "TCSlib." + str(p.relative_to(BASE / "TCSlib").with_suffix("")).replace("/", ".")
        for p in (BASE / "TCSlib").rglob("*.lean")
    }
    non_compiling = sorted(disk_modules - set(full_graph))
    if non_compiling:
        print(f"\nIntentionally skipped — absent from dep_graph (did not compile): {len(non_compiling)}")
        for m in non_compiling:
            print(f"      x {m}")
        print()

    WORK_DIR.mkdir(parents=True, exist_ok=True)
    # Clear stale work files.
    for old in WORK_DIR.glob("*.json"):
        old.unlink()

    units = []
    total_uncovered = 0
    claimed: set[str] = set()  # normalized names already assigned to a work unit
    for module in sorted(modules):
        unit = build_work_unit(module, modules[module], kept_global, covered,
                               args.include_covered, claimed)
        if unit is None:
            continue
        safe = module.replace(".", "_")
        work_file = WORK_DIR / f"{safe}.json"
        work_file.write_text(json.dumps(unit, indent=2), encoding="utf-8")
        n = len(unit["decls"])
        total_uncovered += n
        units.append({
            "module": module,
            "work_file": work_file.relative_to(BASE).as_posix(),
            "target_tex": unit["target_tex"],
            "target_exists": unit["target_exists"],
            "uncovered": n,
        })
        flag = "NEW " if not unit["target_exists"] else "add "
        print(f"  [{flag}] {module}: {n} decl(s) -> {unit['target_tex']}")

    manifest = {
        "generated_from": "dep_graph.json",
        "keep_kinds": sorted(KIND_ENV),
        "skip_kinds": sorted(SKIP_KINDS),
        "total_modules_scanned": len(modules),
        "modules_with_work": len(units),
        "total_uncovered_decls": total_uncovered,
        "already_covered_labels": len(covered),
        "skipped_non_compiling": non_compiling,
        "units": units,
    }
    (WORK_DIR / "manifest.json").write_text(json.dumps(manifest, indent=2), encoding="utf-8")

    print()
    print(f"Modules with work : {len(units)}")
    print(f"Decls to document : {total_uncovered}")
    print(f"Manifest          : {(WORK_DIR / 'manifest.json').relative_to(BASE)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
